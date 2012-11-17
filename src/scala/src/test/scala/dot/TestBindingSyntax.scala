package dot

import org.scalatest._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

trait LambdaSyntax extends AbstractBindingSyntax {
  sealed abstract class Term
  case class Var(n: Name) extends Term
  case class App(fun: Term, arg: Term) extends Term
  case class Lam(abs: \\[Term]) extends Term
}

trait LambdaNominalSyntax extends LambdaSyntax with NominalBindingSyntax { self: LambdaSyntax =>
  implicit val termHasBinders: ContainsBinders[Term] = (tm: Term) => new Nominal[Term] {
    def swap(a: Name, b: Name): Term = {
      tm match {
	case Var(n) => Var(n swap(a, b))
	case App(fun, arg) => App(fun swap(a, b), arg swap(a, b))
	case Lam(abs) => Lam(abs swap(a, b))
      }
    }
    def fresh(a: Name): Boolean = {
      tm match {
	case Var(n) => n fresh(a)
	case App(fun, arg) => fun.fresh(a) && arg.fresh(a)
	case Lam(abs) => abs fresh(a)
      }
    }
  }
}

@RunWith(classOf[JUnitRunner])
class TestBindingSyntax extends Suite with LambdaNominalSyntax {
  val x = Name("x")
  val y = Name("y")
  val z = Name("z")
  def testAlphaEquivalence() = {
    expect(true)(Lam(x\\Var(y)) == Lam(z\\Var(y)))
    expect(false)(Lam(x\\Var(y)) == Lam(y\\Var(x)))
    expect(true)(Lam(x\\Var(x)) == Lam(y\\Var(y)))
  }
}
