package libra

import libra.ProjectedDT.DecisionTreeClassifier
import libra.graphs.TupleGraph
import libra.solvers._
import libra.util.{Logging, Timed}

object Main extends App {

  Timed("Main") {
    Logging.info("Hello!")
    Logging.info {
      val nl = System.lineSeparator()
      val argsStr = this.args.map(arg => s"  $arg").mkString(nl)
      s"Mustar invoked with options:" + nl + argsStr
    }

    if(this.args(0).equals("--dt")) {
      val problemRules = this.args(1)
      val tableName = this.args(2)
      Logging.info("################################################################################")
      Logging.info(s"Solving problem instance: $problemRules")
      println("////////////////////////////////////////////////////////////////////////////////")
      println(s"// Solving problem instance: $problemRules")

      val problem: Problem = Problem(problemRules)
      val (_, relation) = problem.inputRelations.toSet.find(_._1.name == tableName).get
      val (_, labels) = problem.outputRelations.view.toIndexedSeq(0)
      val types = for {d <- relation.schema} yield problem.types(d.toString)

      val dt = new DecisionTreeClassifier(relation, scala.collection.immutable.IndexedSeq(RelationName(problem.name, relation.schema)), types.toList, labels,
        relation.schema.map(d => Variable(d.name, d)), labels.schema.map(d => Variable(d.name, d)))
      Timed("DT") {
        dt.train(1000)
      }
      println("Result: " + dt.dt.predicate)
    } else if(this.args(0).equals("--dtgs")) {
      val useFirstSolution = if (this.args(1).equals("--use-first")) true else false
      val extraArg = if (useFirstSolution) 1 else 0
      this.args.drop(1 + extraArg).foreach(problemRules => {
        Logging.info("################################################################################")
        Logging.info(s"Solving problem instance: $problemRules")
        println("////////////////////////////////////////////////////////////////////////////////")
        println(s"Solving problem instance: $problemRules")

        val problem = Problem(problemRules)
        val solver = new DTGS(problem, useFirstSolution)
        solver.solve()
      })
    } else if(this.args(0).equals("--dtgs_naive")) {
      this.args.drop(1).foreach(problemRules => {
        Logging.info("################################################################################")
        Logging.info(s"Solving problem instance: $problemRules")
        println("////////////////////////////////////////////////////////////////////////////////")
        println(s"Solving problem instance: $problemRules")

        val problem = Problem(problemRules)
        val solver = new NaiveDTGS(problem)
        val rule = solver.solve()
        Logging.info(rule.toString)
      })
    } else if (this.args(0).equals("--csv")) {
      this.args.drop(1).foreach(problemDirectory => {
        Logging.info("################################################################################")
        Logging.info(s"Producing CSVs for problem instance in directory $problemDirectory")
        println("////////////////////////////////////////////////////////////////////////////////")
        println(s"// Producing CSVs for problem instance in directory $problemDirectory")

        val problem = Problem(problemDirectory)
        problem.outputCSV()
      })
    } else {
      this.args.drop(1).foreach(problemRules => {
        Logging.info("################################################################################")
        Logging.info(s"Solving problem instance: $problemRules")
        println("////////////////////////////////////////////////////////////////////////////////")
        println(s"// Solving problem instance: $problemRules")

        val problem = Problem(problemRules)
        val problemSize = (problem.inputRelations ++ problem.outputRelations).values.map(_.numTuples).sum
        if (problemSize <= 1000 || Options.LOG_LARGE_PROBLEMS) {
          Logging.info(problem.toString)
        } else {
          Logging.info(s"Problem consists of $problemSize tuples. Not logging training data!")
        }

        val solver = new SolverV6(problem)
        solver.solve()
      })
    }

    Logging.info("################################################################################")
    Logging.info("Bye!")
  }

}
