abstract class AbstractGraph { graph =>
  type Node <: BasicNode
  type Edge <: BasicEdge

  def newNode(): Node
  def newEdge(from: Node, to: Node): Edge

  class BasicNode { this: Node =>
    def connect(other: Node) = newEdge(this, other)
    val out : graph.type = graph
  }

  class BasicEdge(val from: Node, val to: Node) {
    val out : graph.type = graph
  }
}

class BasicGraph extends AbstractGraph {
  type Node = BasicNode
  type Edge = BasicEdge

  def newNode(): Node =
    new BasicNode()
  def newEdge(from: Node, to: Node): Edge =
    new BasicEdge(from, to)
}

class ColouredGraph extends AbstractGraph {
  type Node = ColouredNode
  type Edge = BasicEdge

  def newNode(): Node =
    new ColouredNode("blue")
  def newEdge(from: Node, to: Node): Edge =
    new BasicEdge(from, to)

  class ColouredNode(var colour: String) extends BasicNode
}

object Test extends App {
  val cg1, cg2 = new ColouredGraph()
  val cn1, cn3 = cg1.newNode()
  val cn2 = cg2.newNode()
  cn1.connect(cn3)
  // cn2.connect(cn3)
  // error: type mismatch;
  // found   : Test.cg1.Node
  //  (which expands to)  Test.cg1.ColouredNode
  // required: Test.cg2.Node
  //  (which expands to)  Test.cg2.ColouredNode
}
