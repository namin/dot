abstract class Graph {
  type Node <: BasicNode
  type Edge <: BasicEdge

  def newNode(): Node
  def newEdge(from: Node, to: Node): Edge

  class BasicNode { this: Node =>
    def connect(other: Node) = newEdge(this, other)
  }

  class BasicEdge(val from: Node, val to: Node)
}

class BasicGraph extends Graph {
  type Node = BasicNode
  type Edge = BasicEdge

  def newNode(): Node =
    new BasicNode()
  def newEdge(from: Node, to: Node): Edge =
    new BasicEdge(from, to)
}

class ColouredGraph extends Graph {
  type Node = ColouredNode
  type Edge = BasicEdge

  def newNode(): Node =
    new ColouredNode("blue")
  def newEdge(from: Node, to: Node): Edge =
    new BasicEdge(from, to)

  class ColouredNode(var colour: String) extends BasicNode
}

abstract class Library {
  def distance(g: Graph)(n1: g.Node, n2: g.Node): Int
  def copyEdge(g: Graph)(e: g.Edge): g.Edge =
    g.newEdge(e.from, e.to)
}

object Test extends App {
  val cg1, cg2 = new ColouredGraph()
  val cn1, cn3 = cg1.newNode()
  val cn2 = cg2.newNode()
  val e = cn1.connect(cn3)
  // cn2.connect(cn3)
  // error: type mismatch;
  // found   : Test.cg1.Node
  //  (which expands to)  Test.cg1.ColouredNode
  // required: Test.cg2.Node
  //  (which expands to)  Test.cg2.ColouredNode
}
