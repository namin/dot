package dot

import org.scalatest._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

trait LambdaTyper extends StandardTyperMonad with LambdaTyperSyntax with LambdaNominalSyntax {
  import TyperMonad._
  override val debugMode = false

  type State = Option[Nothing]
  val initState = None

  def ofT(tm: Term, pt: Expected[Type]): TyperMonad[Unit] = {
    debug("type of " + tm + ":" + pt)
    tm match {
      case Var(x) => for(
	r <- lookup(x);
	_ <- pt := r) yield ()
      case App(fun, arg) => for(
	ty1 <- Infer[Type]("ty1").toMetaVar(MetaType);
	ty2 <- Infer[Type]("ty2").toMetaVar(MetaType);
	_ <- ofT(fun, Check(Fun(ty1, ty2)));
	ty1 <- !ty1;
	ty2 <- !ty2;
	_ <- ofT(arg, Check(ty1));
        _ <- pt := ty2) yield ()
      case Lam(ty1, \\(x, b)) => for(
	ety2 <- Infer[Type]("ty2");
	_ <- assume(x, ty1)(ofT(b, ety2));
	ty2 <- !ety2;
	_ <- pt := Fun(ty1, ty2)) yield ()
    }
  }
  def typecheck(tm: Term): Result[Type] = (for(
    ein <- Infer[Type]("in");
    _ <- ofT(tm, ein);
    in <- !ein) yield in).run getOrElse Failure("")
}

trait LambdaTyperSyntax extends MetaVariablesNominal with LambdaSyntax {
  implicit object MetaType extends MetaVarBuilder[Type, MetaType]("metaTp") {
    def apply(n: String) = new MetaType(n)
  }
  class MetaType(override val name: String) extends Type with MetaVar[Type]
  implicit def eqType(tp1: Type): Equality[Type] = new Equality[Type] {
    def ===(tp2: Type) = (tp1, tp2) match {
      case (x1: MetaType, _) => x1 === tp2
      case (_, x2: MetaType) => x2 === tp1
      case (T(base1), T(base2)) => base1 == base2
      case (Fun(ty1a, ty1b), Fun(ty2a, ty2b)) => ty1a.===(ty2a) && ty1b.===(ty2b)
      case _ => false
    }
  }
}

@RunWith(classOf[JUnitRunner])
class TestTyperMonad extends Suite with LambdaTyper {
  val x = Name("x")
  val y = Name("y")
  val z = Name("z")
  val f = Name("f")
  val ty = T("*")

  def test1() = expect(Success(Fun(ty, ty)))(typecheck(Lam(ty, x\\Var(x))))
  def test2() = expect(Success(Fun(Fun(ty, ty), Fun(ty, ty))))(typecheck(Lam(Fun(ty, ty), f\\Lam(ty, x\\App(Var(f), Var(x))))))
  def test3() = expect(Failure(""))(typecheck(Lam(Fun(ty, ty), f\\Lam(ty, x\\App(Var(x), Var(f))))))
}
