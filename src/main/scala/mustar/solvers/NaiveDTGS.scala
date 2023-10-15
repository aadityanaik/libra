package libra.solvers

import libra.ProjectedDT.{DecisionTree, DecisionTreeClassifier}
import libra.nonrecursiveQueries.{Rule, SPJ}
import libra.util.{Logging, Timed}
import libra.{Problem, SituatedTuple}
import libra.Relation

class NaiveDTGS(problem: Problem) {
  def solve() : Rule = {
    var finalRule: Rule = null
    var finalDT : Option[DecisionTree] = None
    var bound = 1000
    var processedRules = 0

    for(rule <- problem.hypothesisSpace) {
      Timed("tabConstruction") {
        if(bound > rule.body.length) {
          val (labelsRelName, labels) = problem.outputRelations.view.toIndexedSeq(0)
          val table = rule.ruleWithNecessaryVars(problem.types, labelsRelName.schema)
          val tableRes = table(problem.inputRelations)
          val result = tableRes.tuples.map(t => t.slice(0, labelsRelName.schema.length))
          // Logging.info(table)
          val types = for {d <- tableRes.schema} yield problem.types(d.toString)
          val dt = new DecisionTreeClassifier(tableRes, table.body.map(_.relationName), types.toList, labels, table.head.fields, rule.head.fields)
          val numPreds = rule.body.length

          if (result == labels.tuples && bound > numPreds) {
            bound = numPreds
            finalRule = rule
            finalDT = None
          } else {
            Timed("DT") {
              dt.train(bound - numPreds)
            }
            val numConditionals = if (dt.dt != null) dt.dt.numConditions else 0
            val dtResult: Relation = dt.dt.filteredTuples match {
              case Some(p) => {
                val projTuples = p.tuples.map(t => t.slice(0, labelsRelName.schema.length))
                Relation(labelsRelName.schema, projTuples)
              }
              case None => Relation(labelsRelName.schema, Set())
            }

            if (bound > numConditionals + numPreds && dt.dt.root.nonEmpty && dtResult.numTuples > 0) {
              bound = numConditionals + numPreds
              finalRule = rule

              if (!dt.dt.predicate.equals("") && dtResult.numTuples > 0) {
                finalDT = Some(dt.dt)
              } else {
                finalDT = None
              }
            }
          }
          processedRules += 1
        }
      }
    }

    Logging.info(s"$processedRules / ${problem.hypothesisSpace.size} rules processed")
    val outRule = Rule(finalRule.head, finalRule.body, finalDT).minimizeRegisters
    val numConditions = if (finalDT == None) 0  else finalDT.get.numConditions
    println(outRule.toSQLString)
    Logging.info(s"OUTPUT-META\t${outRule.body.size - 1}\t${numConditions}")
    outRule
  }
}
