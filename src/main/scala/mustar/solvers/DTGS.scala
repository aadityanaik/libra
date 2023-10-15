package libra
package solvers

import libra.nonrecursiveQueries.SPJ
import libra.util.{Logging, Timed}
import libra.ProjectedDT.{DecisionTree, DecisionTreeClassifier}
import libra.graphs.TupleGraph.{TupleGraph, EdgeLabel}
import libra.graphs.Edge
import libra.nonrecursiveQueries.UCQ
import libra.nonrecursiveQueries.Rule
import scala.collection.mutable
import java.util.concurrent.atomic.AtomicBoolean
import java.util.ArrayList

class DTGS(problem: Problem, useFirstSolution: Boolean) {
  private val foundSolutions: mutable.ListBuffer[Tuple2[Rule, DecisionTreeClassifier]] = new mutable.ListBuffer()

  val Problem(problemName, inputRelations, outputRelations, types, _) = problem
  lazy val tupleGraph: TupleGraph = graphs.TupleGraph(problem)

  type EnumerationContext = Set[SituatedTuple]

  private val _witnessTuples = collection.mutable.Map[Edge[SituatedTuple, EdgeLabel], EnumerationContext]()
  def witnessTuples(edge: Edge[SituatedTuple, EdgeLabel]): EnumerationContext = {
    _witnessTuples.getOrElseUpdate(edge, graphs.TupleGraph.allWitnessTuples(inputRelations, edge))
  }

  def solve(): Map[RelationName, UCQ] = Timed(s"Solve($problemName)") {
    problem.printHeader(println)

    if ((tupleGraph.vertices.size < 500 && tupleGraph.edges.size < 5000) || Options.LOG_LARGE_GRAPHS) {
      tupleGraph.print(Logging.info)
    } else {
      Logging.info(s"Tuple co-occurrence graph consists of ${tupleGraph.vertices.size} vertices and " +
                   s"${tupleGraph.edges.size} edges. Not logging graph!")
    }

    var soln = Map[RelationName, UCQ]()
    for (relName <- outputRelations.keys) {
      val ucq = solveRelationNonRec(relName)
      soln = soln + (relName -> ucq)
      // solveRelationRec(relName, ucq)
      println()
    }

    Runtime.getRuntime.removeShutdownHook(shutdown)
    soln
  }

  def solveRelationNonRec(outputRelName: RelationName): UCQ = Timed(s"SolveNonRec($problemName)") {
    val outputRelation = outputRelations(outputRelName)

    Logging.info(s"Understanding $outputRelName")
    println(s"// $outputRelName:")

    // This currently will iterate exactly once because multiple
    // tuples in the output relation is not supported
    var ucq = UCQ(outputRelName)
    var unexplainedTuples = outputRelation.tuples
    while (unexplainedTuples.nonEmpty) {
      Logging.info(s"  Yet to explain (${unexplainedTuples.size}):")
      for (t <- unexplainedTuples) {
        Logging.info(s"    ${outputRelName.name}($t)")
      }

      val currTuple = unexplainedTuples.head
      Logging.info(s"  Attempting to explain ${outputRelName.name}($currTuple)")
      val origRule = solveTuple(SituatedTuple(outputRelName, currTuple)).minimizeRegisters
      // val maxRule = Timed {
      //                 origRule.maximizeVars(inputRelations, outputRelation)
      //                         .minimizeLiterals(inputRelations, outputRelation)
      //                         .minimizeRegisters
      //               }
      ucq = ucq + origRule
      Logging.info(s"  origRule: ${origRule.toSQLString}")
      val numConditions = if (origRule.decisionTree.isEmpty) 0 else origRule.decisionTree.get.numConditions
      Logging.info(s"OUTPUT-META\t${origRule.body.size - 1}\t$numConditions")
      // Logging.info(s"  maxRule:  $maxRule")
      // Logging.info(s"  DT:       ${origSPJ.decisionTree.map(_.predicate)}")
      println(origRule.toSQLString)

      // val origSPJResult = origSPJ(inputRelations)
      // val origRuleResult = origRule(inputRelations)
      // val maxRuleResult = maxRule(inputRelations)
      // assert(origSPJResult == origRuleResult)
      // assert(origRuleResult.subsetOf(maxRuleResult))
      // Logging.info(s"  Hypothesis explains:")
      // for (t <- maxRuleResult.tuples) {
      //   if (origRuleResult.contains(t)) {
      //     Logging.info(s"    ${outputRelName.name}($t)")
      //   } else {
      //     Logging.info(s"    ${outputRelName.name}($t)*")
      //   }
      //   assert(outputRelation.contains(t), s"maxResultSPJ contains undesirable tuple $t")
      // }
      // unexplainedTuples = unexplainedTuples -- maxRuleResult.tuples
      unexplainedTuples = unexplainedTuples -- unexplainedTuples
    }
    // assert(ucq(inputRelations) == outputRelation)
    println()

    // ucq = minimizeUCQ(ucq)
    // assert(ucq(inputRelations) == outputRelation)
    // println("// UCQ after minimization:")
    // ucq.queries.foreach(rule => println(s"// $rule"))
    // println()

    ucq
  }

  def minimizeUCQ(ucq: UCQ): UCQ = {
    val totalOutput = ucq(inputRelations)
    val ruleOutputs = ucq.queries.map(rule => rule -> rule(inputRelations)).toMap
    val emptyRelation = Relation(totalOutput.schema, Set())

    var necessaryRules = Set[Rule]()
    var unknownRules = ucq.queries

    while (unknownRules.nonEmpty) {
      val currRule = unknownRules.head
      unknownRules = unknownRules.tail
      val newOutput = (necessaryRules ++ unknownRules).map(ruleOutputs).foldLeft(emptyRelation)(_ ++ _)
      assert(newOutput.subsetOf(totalOutput))
      if (!totalOutput.subsetOf(newOutput)) {
        necessaryRules = necessaryRules + currRule
      }
    }

    UCQ(ucq.outputRelName, necessaryRules)
  }

  def solveTuple(st: SituatedTuple): Rule = {
    val SituatedTuple(outputRelName, currTuple) = st
    val outputRelation = outputRelations(outputRelName)

    require(outputRelName.schema == outputRelation.schema)
    require(outputRelation.schema == currTuple.schema)
    require(outputRelation.contains(currTuple))

    val i = currTuple.fields.size - 1
    val ci = st
    val currTupleSlice = currTuple.slice(0, i + 1)
    val orni = RelationName(outputRelName.name, outputRelName.schema.slice(0, i + 1))
    val outputRelationSlice = outputRelation //.slice(0, i + 1)
    val explanations = solveField(Set[SituatedTuple](), orni, outputRelationSlice, currTupleSlice, ci)
    val ctxdt: Tuple2[Rule, Option[DecisionTree]] = if (this.useFirstSolution)
      (explanations.head._1, Some(explanations.head._2.dt))
      else
      (explanations.last._1, Some(explanations.last._2.dt))
    Logging.info(s"  Explaining indices [0--$i] using ${ctxdt._1}")

    // val ans = contextToSPJOpt(outputRelName, currTuple, ctxdt._1, ctxdt._2.map(_.dt))
    val ans = ctxdt._1
    val ai = ans(inputRelations)
    assert(ai.contains(currTuple))
    // assert(ai.subsetOf(outputRelation))
    new Rule(ans.head, ans.body, ctxdt._2)
  }

  def contextToSPJFast(outputRelName: RelationName, currTuple: DTuple, ctx: EnumerationContext, dt: Option[DecisionTree]): List[SPJ] = Timed {
    // for (c <- currTuple.fields) {
    //   assert(ctx.exists(_.tuple.fields.contains(c)),
    //          s"Error while converting context to SPJ query. " +
    //          s"Target tuple: $currTuple. " +
    //          s"Unable to find constant $c in context $ctx")
    // }

    val ctxVector = ctx.toVector.sortBy(_.toString)
    val joinExpr = ctxVector.map(_.relName)
    val sourceTuple = ctxVector.map(_.tuple).foldLeft(DTuple())(_ ++ _)
    Logging.info(s"outputRelName: $outputRelName")
    Logging.info(s"joinExpr: $joinExpr")
    Logging.info(s"sourceTuple: $sourceTuple")
    Logging.info(s"currTuple: $currTuple")
    SPJ.apply_all(outputRelName, joinExpr, sourceTuple, currTuple, dt)
  }

  def contextToSPJOpt(outputRelName: RelationName, currTuple: DTuple, ctx: EnumerationContext, dt: Option[DecisionTree]): List[SPJ] = Timed {
    // for (c <- currTuple.fields) {
    //   assert(ctx.exists(_.tuple.fields.contains(c)),
    //          s"Error while converting context to SPJ query. " +
    //          s"Target tuple: $currTuple. " +
    //          s"Unable to find constant $c in context $ctx")
    // }

    // TODO: Potentially need to add this back if it degrades
    // performance too much.

    // val permutations = ctx.toVector.permutations
    // val spjs = permutations.map(ctxVector => {
    //   val joinExpr = ctxVector.map(_.relName)
    //   val sourceTuple = ctxVector.map(_.tuple).foldLeft(DTuple())(_ ++ _)
    //   SPJ(outputRelName, joinExpr, sourceTuple, currTuple, dt)
    // })
    // spjs.minBy(_.width)
    val ctxVector = ctx.toVector
    val joinExpr = ctxVector.map(_.relName)
    val sourceTuple = ctxVector.map(_.tuple).foldLeft(DTuple())(_ ++ _)
    SPJ.apply_all(outputRelName, joinExpr, sourceTuple, currTuple, dt)
  }

  def solveField(
    prevCtx: EnumerationContext,
    orni: RelationName,
    outputRelationSlice: Relation,
    currTupleSlice: DTuple,
    targetConstant: SituatedTuple): LazyList[Tuple2[Rule, DecisionTreeClassifier]] = {

    Logging.info(s"Listing paths from $targetConstant")

    val spjFastSPJOptMap = collection.mutable.Map[SPJ, SPJ]()
    val spjOptScoreMap = collection.mutable.Map[SPJ, SPJResultStats]()
    var numPaths = 0L
    var longestPath = 0
    var bound = 20
    val vertices = tupleGraph.vertices
    // require(vertices.contains(targetConstant), s"Unrecognized constant $targetConstant. Vertices = $vertices.")

    val numPossibleOutputTuples = orni.schema.map(problem.domains).map(_.size).product
    val numPossibleBadOutputTuples = numPossibleOutputTuples - outputRelationSlice.numTuples
    Logging.info(s"numPossibleOutputTuples: $numPossibleOutputTuples")
    Logging.info(s"numPossibleGoodTuples: ${outputRelationSlice.numTuples}")
    Logging.info(s"numPossibleBadOutputTuples: $numPossibleBadOutputTuples")

    case class SPJResultStats(rule: Rule, numTuples: Int, numGoodTuples: Int, numBadTuples: Int, numLiterals: Int, dt: DecisionTreeClassifier) {
      val solved: Boolean = numBadTuples == 0
      def score: Double = (numPossibleBadOutputTuples - numBadTuples).toDouble / numLiterals
    }

    case class QueueElement(ctx: EnumerationContext) {
      def numLiterals: Int = ctx.size
      def ends: Set[SituatedTuple] = ctx

      def spjs: List[SPJ] = {
        contextToSPJFast(orni, currTupleSlice, ctx, None)
        // spjFast.map(spj => spjFastSPJOptMap.getOrElseUpdate(spj, contextToSPJOpt(orni, currTupleSlice, ctx, None)))
      }
      lazy val stats: SPJResultStats = spjs.map(spj => spjOptScoreMap.getOrElseUpdate(spj, {
        val rule = spj.toRule
        val numPreds = rule.body.length
        Logging.info(s"Rule: ${rule.toSQLString}")

        val table = rule.ruleWithNecessaryVars(types, orni.schema)
        val tableRes = table(inputRelations)
        val result = tableRes.tuples.map(t => t.slice(0, outputRelationSlice.schema.length))
        Logging.info(s"Computed table: $table")
        val resultTypes = for {d <- tableRes.schema} yield types(d.toString)
        Logging.info(s"Input to DT: $tableRes")
        val dt = new DecisionTreeClassifier(tableRes, table.body.map(_.relationName), resultTypes.toList, outputRelationSlice, table.head.fields, rule.head.fields)

        if (result == outputRelationSlice.tuples) {
          bound = rule.body.length
          val numGoodTuples = (result & outputRelationSlice.tuples).size
          val numBadTuples: Int = (result -- outputRelationSlice.tuples).size
          Logging.info(s"Result matches output: numGoodTuples: $numGoodTuples")
          Logging.info(s"Result matches output: numBadTuples: $numBadTuples")

          SPJResultStats(rule, result.size, numGoodTuples, numBadTuples, numLiterals, dt)
        } else {
          Logging.info(s"output schema: ${outputRelationSlice.schema}")
          Logging.info(s"Result does not match output: numGoodTuples: ${(result & outputRelationSlice.tuples).size}")
          Logging.info(s"Result does not match output: numBadTuples: ${(result -- outputRelationSlice.tuples).size}")
          Logging.info(s"Hashcodes: ${result.map(_.fields.map(x => (x.name, x.domain)))}, ${outputRelationSlice.tuples.toList.map(_.fields.map(x => (x.name, x.domain)))}")
          Timed("DT") {
            Logging.info(s"Current DT depth bound: $bound")
            dt.train(bound - rule.body.length)
          }
          val numConditionals = if (dt.dt != null) dt.dt.numConditions else 0
          Logging.info(s"numConditionals: $numConditionals")
          Logging.info(s"numPreds: $numPreds")
          val dtResult: Relation = dt.dt.filteredTuples match {
            case Some(p) => {
              val projTuples = p.tuples.map(t => t.slice(0, outputRelationSlice.schema.length))
              Relation(outputRelationSlice.schema, projTuples)
            }
            case None => Relation(outputRelationSlice.schema, Set())
          }
          Logging.info(s"Result: $dtResult")
          Logging.info(s"Output tuples: ${outputRelationSlice}")
          Logging.info(s"Computed decision tree: ${dt.dt}")
          if (bound >= numConditionals + numPreds && dtResult == outputRelationSlice) {
            Logging.info(s"Computed decision tree: ${dt.dt}")
            bound = numConditionals + numPreds
            val numGoodTuples = (dtResult & outputRelationSlice).numTuples
            val numBadTuples: Int = (dtResult -- outputRelationSlice).numTuples
            SPJResultStats(rule, dtResult.numTuples, numGoodTuples, numBadTuples, numLiterals, dt)
          } else {
            Logging.info(s"Inner result: $result")
            val numGoodTuples = (result & outputRelationSlice.tuples).size
            val numBadTuples: Int = (result -- outputRelationSlice.tuples).size
            SPJResultStats(rule, result.size, numGoodTuples, numBadTuples, numLiterals, dt)
          }
        }
      })).minBy(res => {
        val numConds = if (res.dt.dt.root.isEmpty) 0 else res.dt.dt.numConditions
        100 * res.numBadTuples + 100 * (outputRelationSlice.numTuples - res.numGoodTuples) + res.numLiterals + numConds
      })
    }
    implicit val pathOrdering: Ordering[QueueElement] = Ordering.by(elem => (-elem.numLiterals, elem.ends.map(_.relName).size))

    val queue = collection.mutable.PriorityQueue[QueueElement]()
    val peaks = collection.mutable.Set[EnumerationContext]()
    def recordQueueElement(ctx: EnumerationContext, parent: Option[QueueElement]): Option[QueueElement] = Timed {
      if (peaks.forall(pk => !ctx.subsetOf(pk))) {
        val elem = QueueElement(ctx)
        if (elem.numLiterals <= bound) {
          Logging.info(s"Adding ctx to queue: ${elem.ctx}")
          queue.enqueue(elem)
          peaks += ctx
          Some(elem)
        } else None
      } else None
    }

    for ((_, relation) <- inputRelations) {
      Logging.info(s"Relation schema: ${relation.schema.toSet}")
      Logging.info(s"Target schema: ${targetConstant.tuple.schema.toSet}")
      Logging.info(s"Intersection schema: ${relation.schema.toSet.intersect(targetConstant.tuple.schema.toSet)}")
    }

    var seedCtx: mutable.Set[Set[SituatedTuple]] = mutable.Set()
    for ((relName, relation) <- inputRelations if relation.schema.toSet.intersect(targetConstant.tuple.schema.toSet).size != 0) {
         // t <- relation.tuples if t.fields.toSet.intersect(targetConstant.tuple.fields.toSet).size != 0) {
      Logging.info(s"Recording seed context with tuple $relName(${DTuple(relation.schema.map(dom => Constant(dom.name, dom)))})...")
      val st = SituatedTuple(relName, DTuple(relation.schema.map(dom => Constant(dom.name, dom))))
      seedCtx.add(prevCtx + st)
    }

    Logging.info(s"Size of seed context: ${seedCtx.size}")
    for (ctx <- seedCtx) {//.toSeq.sortBy(c => c.size)) {
      val result = recordQueueElement(ctx, None)
      result match {
        case Some(elem) => Logging.info(s"Success.") // numTuples: ${elem.stats.numTuples}. " + s"numGoodTuples: ${elem.stats.numGoodTuples}. " +
                                        // s"numBadTuples: ${elem.stats.numBadTuples}.")
        case None => Logging.info("Skipping seed context.")
      }
    }

    def ans: LazyList[QueueElement] = {
      while (queue.nonEmpty) Timed {
        val elem @ QueueElement(ctx) = queue.dequeue()

        if (bound < elem.numLiterals) {
          return LazyList()
        }

        Logging.info("---")
        Logging.info(s"queue.size: ${queue.size}")
        Logging.info(s"Path: ${elem.ctx.toVector.map(_.relName).sortBy(_.toString)}")
        Logging.info(s"Context:")
        for (SituatedTuple(relName, t) <- elem.ctx.toVector.sortBy(_.toString())) {
          Logging.info(s"  $relName($t)")
        }

        var numBad = 1
        if (currTupleSlice.fields.forall(c => elem.ctx.exists(_.tuple.fields.exists(_.domain == c.domain)))) {
          Logging.info(s"numGoodTuples: ${elem.stats.numGoodTuples}")
          Logging.info(s"numBadTuples: ${elem.stats.numBadTuples}")
          Logging.info(s"Size: ${elem.numLiterals}")
          Logging.info(s"Score: ${elem.stats.score} (bad tuples eliminated / literal)")

          numPaths = numPaths + 1
          if ((numPaths & (numPaths - 1L)) == 0L) {
            longestPath = math.max(longestPath, elem.numLiterals - prevCtx.size)
            Logging.info(s"  Enumerated $numPaths paths. Longest path of length $longestPath.")
          }

          numBad = elem.stats.numBadTuples + (outputRelationSlice.numTuples - elem.stats.numGoodTuples)
        }

        for (end <- elem.ends;
             edge <- tupleGraph.edgesToVertex(end);
             t <- witnessTuples(edge)) {
          recordQueueElement(ctx + t, Some(elem))
        }

        if (numBad == 0) {
          Logging.info("Returning element")
          foundSolutions += Tuple2(elem.stats.rule, elem.stats.dt)
          return elem #:: ans
        }
      }
      LazyList()
    }

    ans.map(qe => (qe.stats.rule, qe.stats.dt))
  }

  val shutdown: Thread = new Thread() {
    override def run(): Unit = {
      Logging.info("--- Timeout recieved in DTGS ---")
      val sol = foundSolutions.last
      val ctxdt: Tuple2[Rule, Option[DecisionTree]] = (sol._1, Some(sol._2.dt))
      val ans = ctxdt._1
      val origRule = new Rule(ans.head, ans.body, ctxdt._2)
      val ucq = origRule

      Logging.info(s"  origRule: ${origRule.toSQLString}")
      val numConditions = if (origRule.decisionTree.isEmpty) 0 else origRule.decisionTree.get.numConditions
      Logging.info(s"OUTPUT-META\t${origRule.body.size - 1}\t$numConditions")
      println(origRule.toSQLString)
      println()
      println()
    }
  }

  Runtime.getRuntime.addShutdownHook(shutdown)
}
