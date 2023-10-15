package libra
package nonrecursiveQueries

import libra.util.{Logging, Timed}

import scala.collection.mutable
import libra.ProjectedDT.DecisionTree

case class SPJ(
                outputRelName: RelationName,
                joinExpr: IndexedSeq[RelationName],
                selections: Set[(Int, Int)],
                projections: IndexedSeq[Int],
                decisionTree: Option[DecisionTree]
              ) {

  val joinedSchema: IndexedSeq[Domain] = joinExpr.flatMap(_.schema)
  val outputSchema: IndexedSeq[Domain] = projections.map(joinedSchema)

  // require(selections.forall({ case (i, j) => joinedSchema(i) == joinedSchema(j) }))
  // require(outputRelName.schema == outputSchema)

  for ((i, j) <- selections) {
    require(i < joinedSchema.length)
    require(j < joinedSchema.length)
  }
  for (i <- projections) {
    require(i < joinedSchema.length)
  }

  def apply(inputRelations: Map[RelationName, Relation]): Relation = Timed {
    Logging.info(s"Evaluating $this")
    var currSchema = Vector[Domain]()
    var currTuples = Set(DTuple())

    for (relName <- joinExpr) {
      val prevSchema = currSchema
      currSchema = currSchema ++ relName.schema

      // Optimization 1: Selection pushdowns
      val currSelections = selections.filter({ case (i, j) => i < currSchema.length &&
                                                              j < currSchema.length &&
                                                              (i >= prevSchema.length ||
                                                               j >= prevSchema.length) })
      def currPred(t: DTuple): Boolean = currSelections.forall({ case (i, j) => t(i).name == t(j).name })

      // Optimization 2: Projection pushdowns
      // A selection (i, j) is yet to be applied if either i >= currSchema.length and j >= currSchema.length
      val relevantFields = selections.filter({ case (i, j) => i >= currSchema.length || j >= currSchema.length })
                                     .flatMap({ case (i, j) => Set(i, j) }) ++
                           projections
      def currProject(t: DTuple) : DTuple = {
        val tf = t.fields.zipWithIndex.map({ case (c, i) =>
          if (relevantFields.contains(i)) c else Constant("_", c.domain)
        })
        DTuple(tf)
      }

      currTuples = for (t1 <- currTuples; t2 <- inputRelations(relName).tuples;
                        t12 = t1 ++ t2
                        if currPred(t12) /* Eager selections */)
                   yield currProject(t12) // Eager projections

      if (currTuples.size > SPJ.maxResultSize) {
        SPJ.maxResultSize = currTuples.size
        Logging.info(s"SPJ.maxResultSize: ${SPJ.maxResultSize}")
      }
    }

    def pred(t: DTuple): Boolean = selections.forall({ case (i, j) => t(i).name == t(j).name || t(i).name == "_" || t(j).name == "_" })
    assert(currTuples.forall(pred))

    def project(t: DTuple): DTuple = DTuple(projections.map(t))
    currTuples = currTuples.map(project)

    Relation(outputSchema, currTuples)
  }

  def width: Int = {
    def crossings(k: Int): Int = {
      require(0 <= k && k <= joinExpr.length)
      val numLeftFields = joinExpr.take(k).map(_.schema.length).sum
      val sel1 = selections.filter({ case (i, j) => i < numLeftFields && j >= numLeftFields }).map(_._1)
      val sel2 = selections.filter({ case (i, j) => i >= numLeftFields && j < numLeftFields }).map(_._2)
      val proj = projections.filter(_ < numLeftFields)
      (sel1 ++ sel2 ++ proj).size
    }
    Range(0, joinExpr.length + 1).map(crossings).max
  }

  val _normalizedFieldIndex: mutable.Map[Int, Int] = collection.mutable.Map[Int, Int]()
  def normalizeFieldIndex(fieldIndex: Int): Int = _normalizedFieldIndex.getOrElseUpdate(fieldIndex, {
    val equalFields = collection.mutable.Set(fieldIndex)
    var changed = true
    while (changed) {
      changed = false
      for ((i, j) <- selections if equalFields.contains(i) || equalFields.contains(j)) {
        changed = changed || !equalFields.contains(i) || !equalFields.contains(j)
        equalFields += i
        equalFields += j
      }
    }
    val ans = equalFields.min
    equalFields.foreach(i => _normalizedFieldIndex(i) = ans)
    ans
  })

  val _fieldIndexToLiteralIndex: mutable.Map[Int, Int] = collection.mutable.Map[Int, Int]()
  def fieldIndexToLiteralIndex(fieldIndex: Int): Int = _fieldIndexToLiteralIndex.getOrElseUpdate(fieldIndex, {
    require(0 <= fieldIndex && fieldIndex < joinedSchema.length)
    var numFields = 0
    joinExpr.indices.find(i => {
      numFields = numFields + joinExpr(i).schema.length
      fieldIndex < numFields
    }).get
  })

  val _literalIndexToFieldIndex: mutable.Map[Int, Range] = collection.mutable.Map[Int, Range]()
  def literalIndexToFieldIndices(literalIndex: Int): Range = _literalIndexToFieldIndex.getOrElseUpdate(literalIndex, {
    require(0 <= literalIndex && literalIndex < joinExpr.length)
    val numFieldsLeft = joinExpr.take(literalIndex).map(_.schema.length).sum
    numFieldsLeft until numFieldsLeft + joinExpr(literalIndex).schema.length
  })

  // TODO: Can we use delta debugging or group testing for the following function?
  // TODO: Can we pre-filter the selections to only consider those of the form i < j?
  def minimizeSelections(
                          inputRelations: Map[RelationName, Relation],
                          referenceOutput: Relation
                        ): SPJ = {
    var ans = this
    var currSelections = this.selections
    assert(ans(inputRelations).subsetOf(referenceOutput))
    for ((i, j) <- this.selections) {
      assert(currSelections.contains((i, j)))
      val newAns = SPJ(outputRelName, joinExpr, currSelections -- Set((i, j)), projections, None)
      if (newAns(inputRelations).subsetOf(referenceOutput)) {
        ans = newAns
        currSelections = currSelections -- Set((i, j))
      }
    }
    assert(ans(inputRelations).subsetOf(referenceOutput))
    ans
  }

  def toRule: Rule = {
    var joinedFields = joinedSchema.zipWithIndex
                                   .map({ case (domain, index) =>
                                     // val normalIndex = normalizeFieldIndex(index)
                                     val varName = s"${domain.name(0).toLower}$index" //normalIndex"
                                     Variable(varName, domain)
                                   })

    for ((i, j) <- selections) {
      joinedFields = joinedFields.updated(j, Variable(joinedFields(i).name, joinedFields(j).domain))
    }
    var remainingFields = joinedFields
    val body = for (relName <- joinExpr)
               yield {
                 val litFields = remainingFields.take(relName.schema.size)
                 remainingFields = remainingFields.drop(relName.schema.size)
                 Literal(relName, litFields)
               }
    val head = Literal(outputRelName, projections.map(joinedFields))

    Rule(head, body.toVector, decisionTree)
  }

  override def toString: String = {
    var joinedFields = joinedSchema.zipWithIndex
                                   .map({ case (domain, index) =>
                                     // val normalIndex = normalizeFieldIndex(index)
                                     s"${domain.name(0).toLower}$index" //normalIndex"
                                   })

    for ((i, j) <- selections) {
      joinedFields = joinedFields.updated(j, joinedFields(i))
    }
    var remainingFields = joinedFields
    val bodyStrs = for (relName <- joinExpr)
                   yield {
                     val fieldStrs = remainingFields.take(relName.schema.size)
                     remainingFields = remainingFields.drop(relName.schema.size)
                     s"${relName.name}(${fieldStrs.mkString(", ")})"
                   }
    val headFields = projections.map(normalizeFieldIndex).map(joinedFields)

    s"${outputRelName.name}(${headFields.mkString(", ")}) :- ${bodyStrs.mkString(", ")}."
  }

}

object SPJ {

  var maxResultSize = 0;

  def apply_all(
             outputRelName: RelationName,
             joinExpr: IndexedSeq[RelationName],
             sourceTuple: DTuple,
             targetTuple: DTuple,
             decisionTree: Option[DecisionTree]
           ): List[SPJ] = {
    require(joinExpr.flatMap(_.schema) == sourceTuple.schema)
    require(outputRelName.schema == targetTuple.schema)

    val boundaries = joinExpr.scanLeft(0)((c, r) => c + r.schema.size).tail
    val selections = for (i <- sourceTuple.fields.indices;
                          j <- sourceTuple.fields.indices
                          if (boundaries.find(i < _).get <= j &&
                            sourceTuple(i).domain.name != "" &&
                            sourceTuple(j).domain.name != "" &&
                            sourceTuple(i).domain.name == sourceTuple(j).domain.name))
                     yield (i, j)
    val projections = for (c <- targetTuple.fields)
                      yield {
                        assert(sourceTuple.fields.exists(_.domain == c.domain),
                               s"Error while building SPJ query for target tuple $targetTuple." +
                               s"Cannot find target constant $c in source tuple $sourceTuple")
                        sourceTuple.fields.zipWithIndex.findLast(_._1.domain == c.domain).get._2
                      }

    val groupedSelections = selections.groupBy(s => boundaries.find(b => s._1 < b).get).toList
      .map(_._2.toSet.subsets().map(_.toList).toList.filter(_.length > 0))

    def product(groupedSelections: List[List[List[(Int, Int)]]]): List[List[(Int, Int)]] = groupedSelections match {
      case Nil => List(Nil)
      case h :: t => for (hp <- h; prod <- product(t)) yield hp.appendedAll(prod)
    }
    Logging.info(s"boundaries: $boundaries")
    Logging.info(s"groupedSelections: $groupedSelections")

    val ret = product(groupedSelections).map(s => SPJ(outputRelName, joinExpr, s.toSet, projections, decisionTree))
    Logging.info(s"ret spjs: $ret")
    ret
  }

  def apply(
             outputRelName: RelationName,
             joinExpr: IndexedSeq[RelationName],
             sourceTuple: DTuple,
             targetTuple: DTuple,
             decisionTree: Option[DecisionTree]
           ): SPJ = {
    require(joinExpr.flatMap(_.schema) == sourceTuple.schema)
    require(outputRelName.schema == targetTuple.schema)

    val boundaries = joinExpr.scanLeft(0)((c, r) => c + r.schema.size).tail
    val selections = for (i <- sourceTuple.fields.indices;
                          j <- sourceTuple.fields.indices
                          if (boundaries.find(i < _).get <= j &&
                            sourceTuple(i).domain.name != "" &&
                            sourceTuple(j).domain.name != "" &&
                            sourceTuple(i).domain.name == sourceTuple(j).domain.name))
                     yield (i, j)
    val projections = for (c <- targetTuple.fields)
                      yield {
                        assert(sourceTuple.fields.exists(_.domain == c.domain),
                               s"Error while building SPJ query for target tuple $targetTuple." +
                               s"Cannot find target constant $c in source tuple $sourceTuple")
                        sourceTuple.fields.zipWithIndex.findLast(_._1.domain == c.domain).get._2
                      }

    SPJ(outputRelName, joinExpr, selections.toSet, projections, decisionTree)
  }

}
