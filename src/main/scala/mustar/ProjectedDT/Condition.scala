package libra.ProjectedDT

import libra.util.Timed
import libra.{CompareOp, DTuple, EQ, LT, LTE, Relation, Type, Variable}
import libra.RelationName

/**
 * The Condition class, responsible for carrying details of a condition over which rows of a table are split.
 * @param index Index of the column being compared in the condition
 * @param op    Operator of the comparison, can be one of LT, LTE, EQ
 * @param value Value with which the column is being compared
 */
class Condition(var index: Int, val op: CompareOp, var value: String, var columnVars: IndexedSeq[Variable], var tableName: String) {
  val ordVal: Double = if(!op.equals(EQ)) value.replaceAll("[^\\d]", "").toDouble else 0

  /**
   * Split the rows based on the Condition
   * @param rows  The set of tuples to split
   * @return      Two sets of DTuple type; the first set consists of rows satisfying the condition, and the second consists of rows violating it
   */
  def split(rows: Relation) : (Relation, Relation) = Timed("DTSplit") {
    var condition = (_: DTuple, negate: Boolean) => true
    if(op.equals(LT)) {
      condition = (tup: DTuple, negate: Boolean) => {
        if (tup(index).name.replaceAll("[^\\d]", "") == "") {
          false
        } else {
          negate != (tup(index).name.replaceAll("[^\\d]", "").toDouble < ordVal)
        }
      }
    } else if(op.equals(LTE)) {
      condition = (tup: DTuple, negate: Boolean) => {
        if (tup(index).name.replaceAll("[^\\d]", "") == "") {
          false
        } else {
          negate != (tup(index).name.replaceAll("[^\\d]", "").toDouble <= ordVal)
        }
      }
    } else if(op.equals(EQ)) {
      condition = (tup: DTuple, negate: Boolean) => {
        if (tup(index).name == "") {
          false
        } else {
          negate != (tup(index).name == value)
        }
      }
    }

    val (lp: Relation, rp_p: Relation) = rows.partition(t => condition(t, false))
    val (rp: Relation, _) = rp_p.partition(t => condition(t, true))
    (lp, rp)
  }

  override def toString: String = {
    op match {
      case EQ => "(" + tableName + "." + columnVars(index).domain + " " + op.toString + " " + "\'" + value + "\')"
      case _ => "(" + tableName + "." + columnVars(index).domain + " " + op.toString + " " + value + ")"
    }
  }

  override def equals(obj: Any): Boolean = obj match {
    case other: Condition => other.index.equals(index) &&
      other.op.equals(op) &&
      other.value.equals(value) &&
      other.columnVars.equals(columnVars)
    case _ => false
  }

  override def hashCode(): Int = this.toString.hashCode
}
