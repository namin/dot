abstract class Graph { graph =>
  type Node <: AbstractNode
  type Edge <: AbstractEdge

  def newNode(): Node
  def newEdge(from: Node, to: Node): Edge

  class AbstractEntity {
    val out: graph.type = graph
  }

  abstract class AbstractNode extends AbstractEntity { this: Node =>
    def connect(other: out.Node): out.Edge = newEdge(this, other)
  }

  abstract class AbstractEdge extends AbstractEntity { this: Edge =>
    val from: out.Node
    val to: out.Node
  }
}

class BasicGraph extends Graph {
  class Node extends AbstractNode
  class Edge(val from: Node, val to: Node) extends AbstractEdge

  def newNode(): Node =
    new Node()
  def newEdge(from: Node, to: Node): Edge =
    new Edge(from, to)
}

class ColouredGraph extends Graph {
  class Node(var colour: String) extends AbstractNode
  class Edge(val from: Node, val to: Node) extends AbstractEdge

  def newNode(): Node =
    new Node("blue")
  def newEdge(from: Node, to: Node): Edge =
    new Edge(from, to)
}

object Library {
  def distance(n1: Graph#Node)(n2: n1.out.Node): Int = {
    val e: n1.out.Edge = n1.connect(n2)
    0 // ...
  }
  def copyEdge(e: Graph#Edge): e.out.Edge =
    e.out.newEdge(e.from, e.to)

  def distance2(g: Graph)(n1: g.Node, n2: g.Node): Int = {
    val e: g.Edge = n1.connect(n2)
    0 // ...
  }
  def copyEdge2(g: Graph)(e: g.Edge): g.Edge =
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
  val d1 = Library.distance(cn1)(cn3)
  val d2 = Library.distance2(cg1)(cn1, cn3)
  val e1 = Library.copyEdge(e)
  val e2 = Library.copyEdge2(cg1)(e)
  // these are all type mismatches
  // Library.distance(cn1)(cn2)
  // Library.distance2(cg2)(cn1, cn3)
  // Library.copyEdge2(cg2)(e)
}
