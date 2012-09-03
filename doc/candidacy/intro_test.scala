object Test extends App {
  val c = new AbsCell { type T = Int; val init = 0 }
  println(Library.update(c)(0, 1))
  println(Library.update(c)(0, 1))
  println(Library.update(c)(1, 0))
}
