package libra
package nonrecursiveQueries

case class Literal(relationName: RelationName, fields: IndexedSeq[Variable]) {

  // require(relationName.schema == fields.map(_.domain))
  def schema: IndexedSeq[Domain] = relationName.schema
  override def toString: String = s"${relationName.name}(${fields.mkString(", ")})"
}

object Literal {

  def apply(litString : String, decls: Map[String, RelationName]): Literal = {
    require(litString.endsWith(")"))
    require(litString.contains("("))

    val litSplit = litString.split('(')
    require(litSplit.length == 2)
    val name = litSplit(0).trim
    val args = litSplit(1).slice(0, litSplit(1).length - 1).split(',')
    val relationName = decls(name)
    val fields = for { (arg, argIdx) <- args.zipWithIndex } yield Variable(arg.trim, relationName.schema(argIdx))

    new Literal(relationName, fields.toIndexedSeq)
  }
}
