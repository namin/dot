object Test extends App {
  object coin {
    val r = new util.Random()
    def flip() = r.nextBoolean()
  }
  type XType = {
    type T
    val v: T
    val f: T => T
  }
  val xInt = new {
    type T = Int
    val v = 3
    val f = - (_:T)
  }
  val xBool = new {
    type T = Boolean
    val v = true
    val f = ! (_:T)
  }
  val x: XType = if (coin.flip()) xInt else xBool

  println(x.f(x.v))
}
