trait GraphBase { graph =>
  type Node <: NodeBase
  type Edge <: EdgeBase
  def newNode(): Node
  def newEdge(from: Node, to: Node): Edge

  trait WithOut {
    val out: graph.type = graph
  }
  trait NodeBase extends WithOut { this: Node =>
    def connect(other: out.Node): out.Edge =
      newEdge(this, other)
  }
  trait EdgeBase extends WithOut { this: Edge =>
    val from: out.Node
    val to: out.Node
  }
}

class Graph extends GraphBase {
  class Node extends NodeBase
  class Edge(val from: Node, val to: Node) extends EdgeBase
  def newNode() = new Node
  def newEdge(from: Node, to: Node) = new Edge(from, to)
}

class ColouredGraph extends GraphBase {
  class Node(val colour: String) extends NodeBase
  class Edge(val from: Node, val to: Node) extends EdgeBase
  def newNode() = new Node("blue")
  def newEdge(from: Node, to: Node) = new Edge(from, to)
}

object Library {
  def distance(n1: GraphBase#Node)(n2: n1.out.Node): Int = {
    val e: n1.out.Edge = n1.connect(n2)
    0 // ...
  }
  def copyEdge(e: GraphBase#Edge): e.out.Edge =
    e.out.newEdge(e.from, e.to)

  def distance2(g: GraphBase)(n1: g.Node, n2: g.Node): Int = {
    val e: g.Edge = n1.connect(n2)
    0 // ...
  }
  def copyEdge2(g: GraphBase)(e: g.Edge): g.Edge =
    g.newEdge(e.from, e.to)
}

object Test extends App {
  val cg1, cg2 = new ColouredGraph()
  val cn1 = new cg1.Node("blue")
  val cn2 = new cg2.Node("green")
  val cn3 = new cg1.Node("red")
  val e = cn1.connect(cn3)
  // this is a type mismatch
  // cn2.connect(cn3)

  val d1 = Library.distance(cn1)(cn3)
  val d2 = Library.distance2(cg1)(cn1, cn3)
  val e1 = Library.copyEdge(e)
  val e2 = Library.copyEdge2(cg1)(e)
  // these are all type mismatches
  // Library.distance(cn1)(cn2)
  // Library.distance2(cg2)(cn1, cn3)
  // Library.copyEdge2(cg2)(e)
}
