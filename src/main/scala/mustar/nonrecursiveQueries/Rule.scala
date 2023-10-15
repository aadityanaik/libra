package libra
package nonrecursiveQueries

import libra.util.Timed
import libra.ProjectedDT.DecisionTree
import libra.util.Logging
import scala.collection.mutable

case class Rule(head: Literal, body: IndexedSeq[Literal], decisionTree: Option[DecisionTree]) extends Ordered[Rule] {

  val headVars: Set[Variable] = head.fields.toSet
  val bodyVars: Set[Variable] = body.flatMap(_.fields).toSet
  require(headVars.subsetOf(bodyVars))

  def outputRelName: RelationName = head.relationName
  override def toString: String = {
    decisionTree match {
      case Some(dt) => s"$head :- ${body.mkString(", ")}, ${dt.predicate}."
      case None => s"$head :- ${body.mkString(", ")}."
    }
  }

  def toSQLString: String = {
    val tableLiteral: collection.mutable.HashMap[String, String] = collection.mutable.HashMap[String, String]()
    body.head.fields.foreach(f => tableLiteral += (f.name -> s"T0.${f.domain}"))
    var bodySQL: String = ""
    for ((lit, i) <- body.zipWithIndex) {
      if (i == 0) {
        bodySQL += s"${lit.relationName.name} AS T$i"
      }
      else {
        val joins = lit.fields
          .filter(f => tableLiteral.contains(f.name))
          .map(f => s"T${i}.${f.domain} = ${tableLiteral(f.name)}")
          .mkString(" AND ")
        lit.fields.foreach(f => tableLiteral += (f.name -> s"T${i}.${f.domain}"))
        bodySQL += s" JOIN ${lit.relationName.name} AS T$i ON $joins"
      }
    }
    var selectSQL: String = head.fields
      .map(f => s"T${body.zipWithIndex.find(_._1.fields.contains(f)).get._2}.${f.domain}")
      .mkString(", ")

    val replaced = collection.mutable.HashSet[Int]()
    decisionTree match {
      case Some(dt) if dt.predicate != "" => {
        var predicate = dt.predicate
        Logging.info(s"Predicate: $predicate")
        for ((lit, i) <- body.zipWithIndex) {
          if (!replaced.contains(i)) {
            predicate = predicate.replaceAll(s"\\(${lit.relationName.name}\\.", s"(T$i.")
            replaced.add(i)
          }
        }
        s"SELECT $selectSQL FROM $bodySQL WHERE $predicate"
      }
      case _ => s"SELECT $selectSQL FROM $bodySQL"
    }
  }

  def apply(inputRelations: Map[RelationName, Relation]): Relation = Timed {
    // 30 ms, 11% of running time, 2487 ms total
    var currAsgns = Set(Map[String, Constant]())

    for ((Literal(relName, fields), index) <- body.zipWithIndex) {
      def unify(asgn: Map[String, Constant], t: DTuple): Option[Map[String, Constant]] = {
        var ans = asgn
        for ((v, c) <- fields.zip(t.fields)) {
          if (ans.contains(v.name) && ans(v.name).name != c.name) {
            return None
          }
          ans = ans + (v.name -> c)
        }
        Some(ans)
      }

      val necessaryVars = (body.drop(index + 1).flatMap(_.fields.map(_.name)) ++ head.fields.map(_.name)).toSet

      // By definition, unify involves selection pushdowns
      currAsgns = for (asgn <- currAsgns; t <- inputRelations(relName).tuples; newAsgn <- unify(asgn, t))
                  yield newAsgn.view.filterKeys(necessaryVars).toMap // Projection pushdown
    }

    val ans = currAsgns.map(asgn => DTuple(head.fields.map(x => Constant(asgn(x.name).name, x.domain))))
    Relation(head.schema, ans)
  }

  lazy val usefulVariables: Set[Variable] = {
    val ans = collection.mutable.Set[Variable]()
    ans ++= this.head.fields
    var changed = true
    while (changed) {
      changed = false
      for (literal <- body; v1 <- literal.fields if ans.contains(v1); v2 <- literal.fields) {
        if (!ans.contains(v2)) {
          ans += v2
          changed = true
        }
      }
    }
    ans.toSet
  }

  def keepUsefulLiterals: Rule = {
    val usefulLiterals = body.filter(_.fields.exists(usefulVariables.contains))
    Rule(head, usefulLiterals, this.decisionTree)
  }

  def maximizeVars(inputRelations: Map[RelationName, Relation], referenceOutput: Relation): Rule = {
    var numOccurrences = this.body.flatMap(_.fields).groupBy(v => v).map({ case (v, vs) => v -> vs.length })
    def newVar(domain: Domain): Variable = {
      val pre = domain.name(0).toLower.toString
      var counter = 1
      var ans = Variable(s"$pre$counter", domain)
      while (numOccurrences.contains(ans)) {
        counter = counter + 1
        ans = Variable(s"$pre$counter", domain)
      }
      ans
    }

    var (currLeft, currRight) = (Vector[Literal](), this.body)
    while (currRight.nonEmpty) {
      val Literal(relName, fields) = currRight.head
      currRight = currRight.tail

      var newFields = fields
      for (i <- newFields.indices) {
        val v = newFields(i)
        if (numOccurrences(v) > 1) {
          val nv = newVar(v.domain)
          val nf2 = newFields.updated(i, nv)
          val newLit = Literal(relName, nf2)
          val newRule = Rule(head, (currLeft :+ newLit) ++ currRight, this.decisionTree).keepUsefulLiterals
          if (newRule(inputRelations).subsetOf(referenceOutput)) {
            newFields = nf2
            numOccurrences = numOccurrences + (v -> (numOccurrences(v) - 1)) + (nv -> 1)
          }
        }
      }

      currLeft = currLeft :+ Literal(relName, newFields)
    }
    Rule(head, currLeft, this.decisionTree).keepUsefulLiterals
  }

  def minimizeLiterals(inputRelations: Map[RelationName, Relation], referenceOutput: Relation): Rule = {
    val originalOutput = this(inputRelations)
    // require(originalOutput.subsetOf(referenceOutput))

    var necessaryLiterals = Vector[Literal]()
    var unknownLiterals = this.body
    while (unknownLiterals.nonEmpty) {
      val currLiteral = unknownLiterals.head
      unknownLiterals = unknownLiterals.tail
      val newBodyVars = (necessaryLiterals ++ unknownLiterals).flatMap(_.fields).toSet
      lazy val newRule = Rule(head, necessaryLiterals ++ unknownLiterals, this.decisionTree)
      lazy val newOutput = newRule(inputRelations)
      if (!headVars.subsetOf(newBodyVars) || !newOutput.subsetOf(referenceOutput)) {
        necessaryLiterals = necessaryLiterals :+ currLiteral
      }
    }
    Rule(head, necessaryLiterals, this.decisionTree)
  }

  def crossingFields(numLeftFields: Int): Int = {
    val variablesDefinedBefore = body.take(numLeftFields).last.fields.map(_.name).toSet
    val variablesUsedAfter = body.drop(numLeftFields).head.fields.map(_.name).toSet //++ head.fields
    (variablesDefinedBefore & variablesUsedAfter).size
  }

  lazy val numRegisters: Int = (1 to body.size - 1).map(numLeftFields => crossingFields(numLeftFields)).appended(1).min
  def permutations: Seq[Rule] = body.permutations.map(bodyPrime => Rule(head, bodyPrime, this.decisionTree)).toSeq
  def minimizeRegisters: Rule = {
    permutations.find(_.numRegisters > 0).get
  }
  override def compare(that: Rule): Int = body.map(f => f.toString).sorted.mkString(",").compare(that.body.map(f => f.toString).sorted.mkString(","))

  def ruleWithNecessaryVars(types: Map[String, Type], outputSchema: IndexedSeq[Domain]): Rule = {
    val necessaryVariables = head.fields.concat((for {
      v <- bodyVars
      if (!headVars.contains(v))
      if (!types(v.domain.name).cmpType.equals(NoComp)) || outputSchema.contains(v.domain)
    } yield v).toIndexedSeq)
    val newHead = new Literal(RelationName("table", necessaryVariables.map(v => v.domain)), necessaryVariables)
    new Rule(newHead, body, this.decisionTree)
  }
}

object Rule {

  /**
   * Constructor to build the Rule object from a datalog string representing the rule
   * @param ruleString  Datalog string representing the rule
   */
  def apply(ruleString : String, decls: Map[String, RelationName]): Rule = {
    require(ruleString.contains(":-"), "Rule must contain a head and a body separated by a \":-\"")
    require(ruleString.endsWith("."), "Rule must end with a period (.)")

    val ruleSplit = ruleString.slice(0, ruleString.length - 1).split(":-")
    require(ruleSplit.length == 2, "Rule must have a head and a body")

    val head = Literal(ruleSplit(0).trim, decls)
    val body = ruleSplit(1).trim.split(')').map( bodyLit => {
      var _bodyLit = bodyLit.trim
      if (_bodyLit.startsWith(",")) {
        _bodyLit = _bodyLit.slice(1, _bodyLit.length).trim + ")"
      } else {
        _bodyLit = _bodyLit + ")"
      }
      Literal(_bodyLit, decls)
    })

    Rule(head, body.toIndexedSeq, None)
  }
}
