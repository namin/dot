package scala.dot

import collection.immutable.{Map, HashMap}

import util.binding.frescala.AbstractBindingSyntax
import util.Equalities

/**
 * Created by IntelliJ IDEA.
 * User: adriaan
 * Date: Oct 29, 2009
 * Time: 10:46:51 AM
 * To change this template use File | Settings | File Templates.
 */

class Typer extends StandardTyperMonad with TyperSyntax with NominalBindingSyntax {
  import Terms._
  import Types.{Sel=>TSel, Fun=>FunT, _}
  import Members._
  import TyperMonad.result
  
  def ofT(tm: Term, pt: Expected[Type]): TyperMonad[Unit] =
    ( // Var
      for(Var(x) <- tm;
          tp <- lookup(x);
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
          f  <- MetaType("from"); t  <- MetaType("to");
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
          _   <- expands(x, decls);
          decls <- !decls;
          _   <- assume(x, tc)(for(
                    _ <- wfCtorMems(decls, args);
                    _ <- ofT(b, pt)) yield ()))
      yield ()) 

  // for nom = Check(cb) check that x is fresh in nom
  // for nom = Infer(_)  record that nom must only be unified with something in which x is fresh
  def fresh[T: ContainsBinders](x: Name, nom: Expected[T]) = result(())


  def hasMem(tgt: Term, l: TermLabel, pt: Expected[Type]): TyperMonad[Unit]
    = memberOf(tgt, Check[Decl[Level, Entity]](TypeDecl(l, pt.toMetaVar(MetaTypeBuilder)))) // XXX TODO: why must we pass MetaTypeBuilder explicitly? 

  def memberOf[L <: Level, E <: Entity](tgt: Term, d: Expected[Decl[L, E]]): TyperMonad[Unit]
    = result(())

  def expands(x: Name, nom: Expected[Decls]): TyperMonad[Unit]
    = result(())

  // for pt = Check(tp2) check that tp1 is a subtype of pt
  // for pt = Infer(_)   subsume tp1 to tp2 so that pt can be unified with tp2
  def <:<(tp1: Type, pt: Expected[Type]): TyperMonad[Unit]
    = result(())

  // decls = L_i: S_i..U_i, l_j : V_j
  // args = l_j = v_j
  // check: G |- S_i <: U_i
  //        G |- v_j : V_j
  def wfCtorMems(decls: Decls, args: ValDefs): TyperMonad[Unit]
    = result(())

  // for pt = Check(tp2) check that tp is well-formed
  // for pt = Infer(_)   record that pt must only be unified with a well-formed type
  def wf(pt: Expected[Type]): TyperMonad[Unit]
    = result(())
}


trait TyperSyntax extends MetaVariables with Syntax {
  case class MetaType(override val name: String) extends Type with MetaVar[Type]
  implicit object MetaTypeBuilder extends MetaVarBuilder[Type, MetaType]("metaTp") {
    def make(n: String) = MetaType(n)
  }

  implicit def eqType(tp: Type): Equality[Type] = new Equality[Type] { import Types._
    def ===(o: Type) = (tp, o) match {
      case ( _ , x: MetaType) => x === tp // delegate to MetaType
      case (Sel(tgt, label), Sel(tgto, labelo)) =>  tgt.===(tgto) && label.===(labelo)
//      case (Refine(parent, decls), Refine(parento, declso)) => parent.===(parento) && decls.===(declso)
      case (Fun(from, to), Fun(fromo, too)) => from.===(fromo) && to.===(too)
      case (Intersect(tp1, tp2), Intersect(tp1o, tp2o)) => tp1.===(tp1o) && tp2.===(tp2o)
      case (Union(tp1, tp2), Union(tp1o, tp2o)) => tp1o.===(tp1o) && tp2o.===(tp2o)
      case (Top, Top)    => true
      case (Bottom, Bottom) => true
    }
  }

  implicit def eqTerm(tm: Term): Equality[Term] = new Equality[Term] { import Terms._
    def ===(o: Term) = tm == o // (tm, o) match {}
  }

  implicit def eqLabel[L <: Level](l: Label[L]): Equality[Label[L]] = new Equality[Label[L]] {
    def ===(o: Label[L]) = l == o
  }

  implicit def eqDecl[L <: Level, E <: Entity](d: Members.Decl[L, E]): Equality[Members.Decl[L, E]] = new Equality[Members.Decl[L, E]] {
    def ===(o: Members.Decl[L, E]) = d == o
  }
}