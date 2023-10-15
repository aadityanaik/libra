package libra.ProjectedDT

import libra.util.Logging
import libra.{DTuple, Relation}

case class Partition(var left: Option[Relation], var right: Option[Relation]) {
  def lengths() : (Int, Int) = {
    (left, right) match {
      case (None, None) => (0, 0)
      case (None, _) => (0, right.get.numTuples)
      case (_, None) => (left.get.numTuples, 0)
      case (_, _) => (left.get.numTuples, right.get.numTuples)
    }
  }
}

class Score(var full: Float, var leftScore: Float, var rightScore: Float, leftProb: Float, rightProb: Float) {
  def getProbabilities : (Float, Float) = (leftProb, rightProb)

  override def toString: String = s"$full, $leftScore, $rightScore"
}

/**
 * A class representing the node of a decision tree
 *
 * @param condition The condition for this node
 * @param partition The tuples partitioned by the condition into left (true) and right (false) sets
 * @param score     The scores for this node, including entropy and probabilities
 */
class Node(condition: Condition, var children: (Option[Node], Option[Node]), var partition: Partition, var score: Score) {

  /**
   * Get the conditions for this node and all its children in the form of a predicate
   * @return String representing predicate
   */
  def predicate() : String = {
    val probabilities = score.getProbabilities

    children match {
      case (None, None) =>
        probabilities match {
          case (1, _) => condition.toString
          case (_, 1) => "NOT" + condition.toString
          case (_, _) =>
            require(false)
            ""
        }
      case (None, right: Some[Node]) =>
        probabilities match {
          case (1, _) => "(" + condition.toString + " OR " + right.get.predicate() + ")"
          case (_, _) => "( NOT" + condition.toString + " AND " + right.get.predicate() + ")"
        }
      case (left: Some[Node], None) =>
        probabilities match {
          case (_, 1) => "( NOT" + condition.toString + " OR " + left.get.predicate() + ")"
          case (_, _) => "(" + condition.toString + " AND " + left.get.predicate() + ")"
        }
      case (left: Some[Node], right: Some[Node]) =>
        "(" + condition.toString + " AND " + left.get.predicate() + ") OR " + "( NOT" + condition.toString + " AND " + right.get.predicate() + ")"
    }
  }

  def filteredTuples() : Option[Relation] = {
    val probabilities = score.getProbabilities

    children match {
      case (None, None) => {
        probabilities match {
          case (a, b)  if (a >= b) => partition.left
          case (a, b)  if (a < b) => partition.right
        }
      }
      case (Some(c1), None) => {
        probabilities match {
          case (_, 1) => (partition.right ++ c1.filteredTuples).reduceOption(_ ++ _)
          case (_, _) => c1.filteredTuples()
        }
      }
      case (None, Some(c2)) => {
        probabilities match {
          case (1, _) => (partition.left ++ c2.filteredTuples).reduceOption(_ ++ _)
          case (_, _) => c2.filteredTuples()
        }

      }
      case (Some(c1), Some(c2)) => (c1.filteredTuples() ++ c2.filteredTuples()).reduceOption(_ ++ _)
    }
  }

  override def toString: String = "(" + condition.toString + ", " + score.toString + ", " + children.toString() + ")"

  def numConditions : Int = {
    children match {
      case (None, None) => 1
      case (None, right: Some[Node]) => right.get.numConditions + 1
      case (left: Some[Node], None) => left.get.numConditions + 1
      case (left: Some[Node], right: Some[Node]) => left.get.numConditions + right.get.numConditions + 1
    }
  }
}

class DecisionTree {
  var root : Option[Node] = None

  override def toString: String = root match {
    case node : Some[Node] => node.get.toString()
    case None => ""
  }

  def predicate : String = root match {
    case node : Some[Node] => node.get.predicate()
    case None => ""
  }

  def filteredTuples : Option[Relation] = root match {
    case node : Some[Node] => node.get.filteredTuples()
    case None => None
  }

  def numConditions : Int = root match {
    case node : Some[Node] => node.get.numConditions
    case None => 0
  }
}
