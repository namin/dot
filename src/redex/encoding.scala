object pets {
  trait Pet
  trait Dog extends Pet
  trait Cat extends Pet
  trait Poodle extends Dog
  trait Dalmatian extends Dog
}

object choices {
  trait Alt {
    type C
    type A <: C
    type B <: C
    val choose : A => B => C
  }
  def pickFirst[Cp,Ap<:Cp,Bp<:Cp] = new Alt {
    type C = Cp
    type A = Ap
    type B = Bp
    val choose = (a: A) => (b: B) => a
  }
  def pickLast[Cp,Ap<:Cp,Bp<:Cp] = new Alt {
    type C = Cp
    type A = Ap
    type B = Bp
    val choose: A => B => B = a => b => b
  }
}

object Main extends App {
  import pets._
  import choices._

  val potty = new Poodle { override def toString = "potty" }
  val dotty = new Dalmatian { override def toString = "dotty" }

  val picker = pickLast[Dog,Poodle,Dalmatian]
  val p: picker.A = potty
  val r: picker.B = picker.choose(potty)(dotty)
  println(r)
  //type error: println(picker.choose(dotty)(potty))
}
