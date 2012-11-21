package dot

import org.scalatest._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

trait LambdaSyntax extends AbstractBindingSyntax {
  sealed abstract class Term
  case class Var(n: Name) extends Term
  case class App(fun: Term, arg: Term) extends Term
  case class Lam(ty: Type, abs: \\[Term]) extends Term

  abstract class Type
  case class T(base: String) extends Type
  case class Fun(ty1: Type, ty2: Type) extends Type
}

trait LambdaNominalSyntax extends LambdaSyntax with NominalBindingSyntax { self: LambdaSyntax =>
  implicit val termHasBinders: ContainsBinders[Term] = (tm: Term) => new Nominal[Term] {
    def swap(a: Name, b: Name): Term = {
      tm match {
        case Var(n) => Var(n swap(a, b))
        case App(fun, arg) => App(fun swap(a, b), arg swap(a, b))
        case Lam(ty, abs) => Lam(ty, abs swap(a, b))
      }
    }
    def fresh(a: Name): Boolean = {
      tm match {
        case Var(n) => n fresh(a)
        case App(fun, arg) => fun.fresh(a) && arg.fresh(a)
        case Lam(ty, abs) => abs fresh(a)
      }
    }
  }
}

trait LambdaSubstitution extends LambdaNominalSyntax {
  implicit def scopedIsTermSubstable[T](in: \\[T])(implicit wSubs: T => Substable[Term, T], wNom: T => Nominal[T]): Substable[Term, \\[T]] = scopedIsSubstable[T, Term, T](in)

  implicit def termIsSubstable(in: Term): Substable[Term, Term] = new Substable[Term, Term] {
    def subst(from: Name, to: Term): Term = in match {
      case Var(`from`) => to
      case Var(_) => in
      case App(fun, arg) => App(fun subst(from, to), arg subst(from, to))
      case Lam(ty, abs) => Lam(ty, abs subst(from, to))
    }
  }
}

@RunWith(classOf[JUnitRunner])
class TestBindingSyntax extends Suite with LambdaNominalSyntax with LambdaSubstitution {
  val x = Name("x")
  val y = Name("y")
  val z = Name("z")
  val ty = T("*")

  def testAlphaEquivalence() = {
    expect(true)(Lam(ty, x\\Var(y)) == Lam(ty, z\\Var(y)))
    expect(false)(Lam(ty, x\\Var(y)) == Lam(ty, y\\Var(x)))
    expect(true)(Lam(ty, x\\Var(x)) == Lam(ty, y\\Var(y)))
  }
  def testSubstitution() = {
    expect(Lam(ty, y\\Var(z)))(Lam(ty, y\\Var(x)) subst(x, Var(z)))
    expect(Lam(ty, x\\Var(x)))(Lam(ty, x\\Var(x)) subst(x, Var(z)))
  }
}
