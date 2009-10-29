package scala.dot

import util.binding.frescala.AbstractBindingSyntax
import collection.immutable.{Map, HashMap}

/**
 * Created by IntelliJ IDEA.
 * User: adriaan
 * Date: Oct 29, 2009
 * Time: 10:46:51 AM
 * To change this template use File | Settings | File Templates.
 */

trait Metavariables extends AbstractBindingSyntax with TyperMonad {
  trait Equality[T] {
	  def ===(a: T): Boolean
  }

  // deep equality that also does unification of MetaVar's
  trait CheckingEquality[A] extends Equality[A] {
    def ===(other: A): Boolean
  }

  implicit def OptionCEq[T : CheckingEquality](self: Option[T]): CheckingEquality[Option[T]] = new CheckingEquality[Option[T]] {
    def ===(other: Option[T]): Boolean = (for( s <- self; o <- other) yield s === o) getOrElse(true)
  }

  implicit def NameCEq(self: Name): CheckingEquality[Name] = new CheckingEquality[Name] {
    def ===(other: Name): Boolean = self == other
  }

  implicit def AbsCEq[T : CheckingEquality](x: \\[T]): CheckingEquality[\\[T]] = new CheckingEquality[\\[T]] {
    def ===(a: \\[T]): Boolean = x.gequals[CheckingEquality](a)
  }

  // facilities for bidirectional type checking (logic programming, really)
  abstract class Expected[A : CheckingEquality] {
    def :=(tp: A): TyperMonad[Unit]
    def unary_! : TyperMonad[A]
  }

  def Infer[A : CheckingEquality](n: String): Infer[A] = new Infer[A](n: String)
  class Infer[A : CheckingEquality](val name: String) extends Expected[A] {
    private var tp: Option[A] = None
    def :=(tp: A): TyperMonad[Unit] = TyperMonad.result(this.tp=Some(tp))
    def unary_! = tp map {TyperMonad.result(_)} getOrElse TyperMonad.fail("inference of "+name+" failed")
  }

  case class Check[A : CheckingEquality](val tp: A) extends Expected[A] {
    def :=(tp: A): TyperMonad[Unit] =
      if(this.tp === tp) {
        println("check: "+this.tp+" == "+tp)
        TyperMonad.result(())
      } else {
        println("check: "+this.tp+" != "+tp)
        TyperMonad.fail("type checking failed")
      }
    def unary_! = TyperMonad.result(tp)
  }

  // meta variable used by the type checker
  trait MetaVar[T] extends CheckingEquality[T] { self: T with MetaVar[T] =>
    val name: String
    var v: Option[T]

    def swap(a: Name, b: Name) = this
    def fresh(a: Name) = true
    def supp = List()

    // if this variable unifies with o, return Some(o)  -- TODO: use dependent method type Option[o.type]
    def unifies(o: T): Option[T]

    def unify(o: T): Boolean = {
      assert(v.isEmpty)
      println("unified "+this+" to "+o)
      v = unifies(o)
      !v.isEmpty
    }

    def unary_! = v map {TyperMonad.result(_)} getOrElse TyperMonad.fail("meta variable "+name+" not set")

    // if set, check against that -- if not set, unify with o and return true
    override def ===(o: T) = // v map{_ === o} getOrElse(unify(o))
      v match {
        case Some(v) => !unifies(v).isEmpty
        case None => unify(o)
      }

  }
}

class Typer extends NominalBindingSyntax with Metavariables {
  import Terms._
  import Types.{Sel=>TSel, Fun=>FunT, _}
  import Members._

  def ofT(tm: Term, pt: Expected[Type]): TyperMonad[Unit] =
    ( // Var
      for(Var(x) <- tm;
          tp <- lookup(X);
          _  <- wf(pt);
          _  <- <:<(tp, pt))
      yield ()) ++ (
      // Sel
      for(Sel(t, l) <- tm;
          _  <- hasMem(t, l, pt))
      yield ()) ++ (
      // App
      for(App(fun, arg) <- tm;
          // check G |- fun : f => t, but don't know f and t --> make new meta-variables
          f  <- newMetaType("from"); t  <- newMetaType("to");
          _  <- ofT(fun, Check(FunT(f, t)));
          f  <- !f ; t <- !t;               // force the meta-variables --> must have been unified or something is wrong
          _  <- ofT(arg, Check(f));         // check that the argument has the expected type
          _  <- pt := t)
      yield ()) ++ (
      // Abs
      for(Fun(ta, \\(x, b)) <- tm;
          _          <- wf(Check(ta));
          tr  = Infer[Type]("tf");
          _   <- fresh(x, tr);
          _   <- assume(x, ta)(ofT(b, tr));
          tr  <- !tr;
          _   <- <:<(FunT(ta, tr), pt);
          _   <- wf(pt))
      yield ()) ++ (
      // New
      for(New(tc, \\(x, (args, b))) <- tm; // parsing has already checked tc is a class type
          _   <- wf(Check(tc));
          _   <- fresh(x, pt);
          decls = Infer[Decls]("decls");
          _   <- unfold(x, decls);
          decls <- !decls;
          _   <- assume(x, tc)(for(
                    _ <- wfCtorMems(decls, args);
                    _ <- ofT(b, pt)) yield ()))
      yield ()) 

  // for nom = Check(cb) check that x is fresh in nom
  // for nom = Infer(_)  record that nom must only be unified with something in which x is fresh
  def fresh[T: Nominal](x: Name, nom: Expected[T])

  // decls = L_i: S_i..U_i, l_j : V_j
  // args = l_j = v_j
  // check: G |- S_i <: U_i
  //        G |- v_j : V_j
  def wfCtorMems(decls: Decls, args: ValDefs)

  // for pt = Check(tp2) check that tp is well-formed
  // for pt = Infer(_)   record that pt must only be unified with a well-formed type
  def wf(pt: Expected[Type])


  // for pt = Check(tp2) check that tp1 is a subtype of pt
  // for pt = Infer(_)   subsume tp1 to tp2 so that pt can be unified with tp2
  def <:<(tp1: Type, pt: Expected[Type])

  def hasMem(tgt: Term, l: TermLabel, pt: Expected[Type])

  type State = Unit
  val initState = ()

  // gamma, maps Name to Type
  type Env = Map[Name, Type]
  lazy val initEnv = HashMap()

  def assume[A](vr: Name, tp: Type)(in: TyperMonad[A]): TyperMonad[A] = TyperMonad{x =>
    in(x mapEnv {_ + (vr -> tp)})
  }

  def getGamma: TyperMonad[Env] = TyperMonad{_ mapEnvTo(x => Success(x)) }

  def lookup(n: Name): TyperMonad[Type] = getGamma >>= {
    _.get(n) match {
    case Some(t) => println("lu"+t); result(t)
    case None => fail("")
    }
  }

}