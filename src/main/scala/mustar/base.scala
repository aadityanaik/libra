package libra

import libra.util.Logging

case class Domain(name: String) {
  override def toString: String = name
}

// TODO: CHANGE NAME TO BE A STRING OR A DOUBLE for efficiency
sealed abstract class Parameter {
  def name: String
  def domain: Domain
  override def toString: String = name
}

case class Constant(name: String, domain: Domain) extends Parameter {
  override def equals(obj: Any): Boolean = {
    // Logging.info(s"Comparing equality between $this and $obj")
    obj match {

      case c: Constant => (this.name.toDoubleOption, c.name.toDoubleOption) match {
        case (d1: Some[Double], d2: Some[Double]) => (d1.get == d2.get && this.domain == c.domain)
        case (_, _) => this.name == c.name && this.domain == c.domain
      }
      case _ => false
    }
  }

  override def hashCode(): Int = {
    // Logging.info(s"Calculating hash for $name")
    name.toDoubleOption match {
      case Some(d) => (d, domain).hashCode
      case _ => (name, domain).hashCode
    }
  }
}
case class Variable(name: String, domain: Domain) extends Parameter

case class
DTuple(fields: IndexedSeq[Constant]) extends (Int => Constant) {
  def schema: IndexedSeq[Domain] = fields.map(_.domain)
  def apply(i: Int): Constant = fields(i)
  override def toString: String = fields.mkString("(", ", ", ")")
  def ++(that: DTuple): DTuple = DTuple(this.fields ++ that.fields)
  def slice(from: Int, until: Int): DTuple = DTuple(fields.slice(from, until))
  def project(indices: List[Int]) : DTuple = DTuple((for {
    index <- indices
  } yield fields(index)).toIndexedSeq)
}

object DTuple {
  private val unitTuple: DTuple = DTuple(Vector())
  def apply(): DTuple = unitTuple
}

case class Relation(schema: IndexedSeq[Domain], tuples: Set[DTuple]) {
  // require(tuples.forall(_.schema == schema))
  // TODO: Logging.reportSize("schema, tuples.size")

  def numTuples: Int = tuples.size

  def ++(that: Relation): Relation = {
    require(this.schema == that.schema)
    Relation(schema, tuples ++ that.tuples)
  }

  def --(that: Relation): Relation = {
    require(this.schema == that.schema)
    Relation(schema, tuples -- that.tuples)
  }

  def &(that: Relation): Relation = {
    require(this.schema == that.schema)
    Relation(schema, tuples & that.tuples)
  }

  def slice(from: Int, until: Int): Relation = {
    val slicedSchema = schema.slice(from, until)
    val slicedTuples = tuples.map(_.slice(from, until))
    Relation(slicedSchema, slicedTuples)
  }

  def contains(t: DTuple): Boolean = {
    require(this.schema == t.schema)
    this.tuples.contains(t)
  }

  def subsetOf(that: Relation): Boolean = {
    require(this.schema == that.schema)
    this.tuples.subsetOf(that.tuples)
  }

  def project(indices: List[Int]) : Relation = {
    val projectedSchema = (for {i <- indices} yield schema(i)).toIndexedSeq
    val projectedTuples = for {tup <- tuples} yield tup.project(indices)


    Relation(projectedSchema, projectedTuples)
  }

  def partition(condition: DTuple => Boolean) : (Relation, Relation) = {
    var (trueSet, falseSet) = tuples.partition(condition)
    (Relation(schema, trueSet), Relation(schema, falseSet))
  }
}

case class RelationName(name: String, schema: IndexedSeq[Domain]) {
  override def toString: String = s"$name(${schema.mkString(", ")})"
}

sealed trait CompareType
case object Categorical extends CompareType {
  override def toString: String = "CAT"
}
case object Ordered extends CompareType {
  override def toString: String = "ORD"
}
case object NoComp extends CompareType {
  override def toString: String = "NoComp"
}

case class Type(name: String, var cmpType: CompareType)

case class SituatedTuple(relName: RelationName, tuple: DTuple)

sealed trait CompareOp
case object LT extends CompareOp {
  override def toString: String = "<"
}
case object LTE extends CompareOp {
  override def toString: String = "<="
}
case object EQ extends CompareOp {
  override def toString: String = "="
}

