class Graph { graph =>
  class WithOut {
    val out: graph.type = graph
  }

  class Node extends WithOut {
    def connect(other: out.Node): out.Edge =
      new out.Edge(this, other)
  }

  class Edge(f: Node, t: Node) extends WithOut {
    val from: out.Node = f
    val to: out.Node = t
  }

  def newNode() = new Node
}

class ColouredGraph extends Graph {
  class Node extends super.Node {
    var colour: String = "blue"
  }

  override def newNode() = new Node
}

object Library {
  def distance(n1: Graph#Node)(n2: n1.out.Node): Int = {
    val e: n1.out.Edge = n1.connect(n2)
    0 // ...
  }
  def copyEdge(e: Graph#Edge): e.out.Edge =
    new e.out.Edge(e.from, e.to)

  def distance2(g: Graph)(n1: g.Node, n2: g.Node): Int = {
    val e: g.Edge = n1.connect(n2)
    0 // ...
  }
  def copyEdge2(g: Graph)(e: g.Edge): g.Edge =
    new g.Edge(e.from, e.to)
}

object Test extends App {
  val cg1, cg2 = new ColouredGraph()
  val cn1, cn3 = new cg1.Node()
  val cn2 = new cg2.Node()
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
