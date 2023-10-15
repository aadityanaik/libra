package libra.graphs

import libra.{Problem, Relation, RelationName, SituatedTuple}
import libra.graphs.ConstantGraph.EdgeLabel
import libra.util.Logging
import libra.DTuple
import libra.util.Timed
import libra.Constant

object TupleGraph {
  case class EdgeLabel(srcRel: RelationName, srcIndex: Int, sinkRel: RelationName, sinkIndex: Int) {
    override def toString: String = s"(${srcRel.name}, $srcIndex, ${sinkRel.name}, $sinkIndex)"
  }

  type TupleGraph = Graph[SituatedTuple, EdgeLabel]

  def apply(problem: Problem) : TupleGraph = {
    val vertices = (for {
      (relName, rel) <- problem.inputRelations
      // t <- rel.tuples
    } yield SituatedTuple(relName, DTuple(rel.schema.map(dom => Constant(dom.name, dom))))).toSet

    // TODO make this better and more efficient
    val edges = for {
      src <- vertices
      snk <- vertices
      if !src.equals(snk)
      srcIdx <- src.tuple.fields.indices
      snkIdx <- snk.tuple.fields.indices
      if src.tuple(srcIdx).name.equals(snk.tuple(snkIdx).name)
      if !src.tuple(srcIdx).name.equals("") && !src.tuple(srcIdx).name.equals("")
      label = EdgeLabel(src.relName, srcIdx, snk.relName, snkIdx)
    } yield Edge(src, label, snk)

    Logging.info(edges.size, vertices.size)

    Graph(vertices, edges)
  }

  def allWitnessTuples(
                        inputRelations: Map[RelationName, Relation],
                        edge: Edge[SituatedTuple, EdgeLabel]
                      ): Set[SituatedTuple] = Timed {
    val Edge(src, EdgeLabel(srcRelName, srcIndex, sinkRelName, sinkIndex), sink) = edge

    Set(src)
  }
}
