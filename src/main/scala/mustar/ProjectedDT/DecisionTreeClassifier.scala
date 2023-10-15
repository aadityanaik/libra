package libra.ProjectedDT

import libra.util.{Logging, Timed}
import libra.{Categorical, DTuple, Domain, EQ, LT, LTE, Ordered, Relation, Type, Variable}

import scala.collection.mutable
import libra.RelationName

/**
 * Class for training the Decision Tree Classifier
 * @param relation  The table to run the classifier on
 * @param types     The types of the columns of the table
 * @param labels    The positive output labels for the classifier
 */
class DecisionTreeClassifier(
  relation: Relation,
  allRels: IndexedSeq[RelationName],
  types: List[Type],
  labels: Relation,
  relVars : IndexedSeq[Variable],
  labelVars: IndexedSeq[Variable]) {

  var dt = new DecisionTree()
  require(relation.schema.size == types.size)

  var conditions: mutable.Set[Condition] = mutable.Set[Condition]()
  var qLabels : Relation = labels
  var explained : Relation = Relation(labels.schema, Set())

  for(tup: DTuple <- relation.tuples) {
    // Logging.info(tup)
    for((c, i) <- tup.fields.view.zipWithIndex) {
      types(i).cmpType match {
        case Categorical =>
          var cond = new Condition(i, EQ, c.name, relVars, allRels.find(_.schema.contains(c.domain)).get.name)
          Logging.info(s"All rels: ${allRels.map(_.schema)}")
          Logging.info(s"Found ${c.domain} in ${allRels.find(_.schema.contains(c.domain)).get.name}")
          conditions.add(cond)
        case Ordered =>
          try {
            // Just as a way to check that c can be converted to a double
            c.name.replaceAll("[^\\d]", "").toDouble
            conditions.add(new Condition(i, LT, c.name, relVars, allRels.find(_.schema.contains(c.domain)).get.name))
            conditions.add(new Condition(i, LTE, c.name, relVars, allRels.find(_.schema.contains(c.domain)).get.name))
          } catch {
            case e: NumberFormatException => Logging.info(e)
          }
        case _ =>
      }
    }
  }

  val projectionIdxs: List[Int] =  labelVars.view.map(v => relVars.view.zipWithIndex.find(_._1.name == v.name).get._2).toList

  def entropy(tab: Relation) : (Double, Double) = {
    // require(tab.schema.equals(labels.schema))

    val unexplained = tab.numTuples.toDouble - numExplained(tab).toDouble
    val desiredAndProduced = numOPlus(tab).toDouble
    // val desiredAndProduced = (tab & qLabels).numTuples
    val p = if (tab.numTuples > 0) desiredAndProduced / unexplained else 0
    if (p == 0 || p == 1) {
      (0, p)
    } else {
      (-p * math.log(p) - (1-p) * math.log(1-p), p)
    }
  }

  def numOPlus(subtable: Relation): Int = {
    subtable.tuples.toList.map(tup => {
      if (qLabels.tuples.contains(tup.project(projectionIdxs))) 1 else 0
    }).sum
  }

  def numExplained(subtable: Relation): Int = {
    subtable.tuples.toList.map(tup => {
      if (explained.tuples.contains(tup.project(projectionIdxs))) 1 else 0
    }).sum
  }

  def differences(subtable: Relation, leftSplit: Relation, rightSplit: Relation) :
  (Relation, Relation, Relation) = Timed("DTDifference") {
    val projectedSubtable = subtable.project(projectionIdxs)
    val projectedLeft = leftSplit.project(projectionIdxs)
    val projectedRight = rightSplit.project(projectionIdxs)

    (projectedSubtable, projectedLeft, projectedRight)
  }

  def entropies(subtable: Relation, leftSplit: Relation, rightSplit: Relation) :
  (Double, Double, Double, Double, Double, Double, Relation) = Timed("DTEntropy") {
    // var (projectedSubtable, projectedLeft, projectedRight) = differences(subtable, leftSplit, rightSplit)
    val (h, p) = entropy(subtable)
    var (ht, pt) = entropy(leftSplit)
    var (hf, pf) = entropy(rightSplit)
    val denominator = subtable.numTuples.toDouble - numExplained(subtable)//projectedLeft.numTuples.toDouble + projectedRight.numTuples.toDouble

    // Not possible for (pt == 1 && pf == 1)
    val explained = if (pt == 1) {
      // projectedLeft
      leftSplit.project(projectionIdxs)
    } else if (pf == 1) {
      // projectedRight
      rightSplit.project(projectionIdxs)
    } else {
      Relation(labels.schema, Set())
    }

    (
      h,
      ((leftSplit).numTuples / denominator) * ht,
      ((rightSplit).numTuples / denominator) * hf,
      p,
      pt,
      pf,
      explained)
  }

  def findCondition(subtable: Relation) : Option[Node] = Timed("DTFind") {
    var splitNode : Option[Node] = None
    var curr_explained : Relation = Relation(labels.schema, Set())

    if(subtable.numTuples > 0 && conditions.nonEmpty) {
      for(condition <- conditions) {

        val (left, right) = condition.split(subtable)
        Logging.info(s"Left: $left")
        Logging.info(s"Right: $right")
        val (h, ht, hf, p, pt, pf, explained_cand) = entropies(subtable, left, right)
        Logging.info(s"Left prob: $pt")
        Logging.info(s"Right prob: $pf")

        val informationGain = h - ht - hf
        Logging.info(s"Processing $condition, info gain is $h - $ht - $hf")

        splitNode match {
          case None => {
            splitNode = Some(
              new Node(
                condition = condition,
                children = (None, None),
                partition = new Partition(Some(left), Some(right)),
                score = new Score(informationGain.toFloat, ht.toFloat, hf.toFloat, pt.toFloat, pf.toFloat)))
            curr_explained = explained_cand
          }
          case node : Some[Node] => if (node.get.score.full < informationGain) {
            splitNode = Some(new Node(
              condition = condition,
              children = (None, None),
              partition = new Partition(Some(left), Some(right)),
              score = new Score(informationGain.toFloat, ht.toFloat, hf.toFloat, pt.toFloat, pf.toFloat)))
            curr_explained = explained_cand
          }
        }
      }
      qLabels --= curr_explained
      explained = curr_explained
    }

    Logging.info(s"Split node is: $splitNode")
    splitNode
  }

  def train(maxDepth: Int) : Unit = {
    qLabels = labels

    if (maxDepth > 0) {
      dt.root = findCondition(relation)
    }
    val evalQueue = mutable.Queue[Node]()
    if(dt.root.nonEmpty) evalQueue.enqueue(dt.root.get)

    var depth = 0
    while(qLabels.numTuples > 0 && evalQueue.nonEmpty && (maxDepth < 0 || depth < maxDepth)) {
      val node = evalQueue.dequeue()
      val (leftScore, rightScore) = (node.score.leftScore, node.score.rightScore)
      val partitions = node.partition
      var (leftNode, rightNode) = node.children

      if(leftScore != 0 && entropy(partitions.left.get)._1 != 0) {
        leftNode = findCondition(partitions.left.get)
        if(leftNode.nonEmpty) evalQueue.enqueue(leftNode.get)
      }
      if(rightScore != 0 && entropy(partitions.right.get)._1 != 0) {
        rightNode = findCondition(partitions.right.get)
        if(rightNode.nonEmpty) evalQueue.enqueue(rightNode.get)
      }
      node.children = (leftNode, rightNode)
      depth += 1
    }
  }

  override def toString: String = dt.toString

}
