package scala.dot

import collection.immutable.{Map, HashMap}

import scala.util.binding.frescala.AbstractBindingSyntax
import scala.util.Equalities

/**
 * Created by IntelliJ IDEA.
 * User: adriaan
 * Date: Oct 29, 2009
 * Time: 10:46:51 AM
 * To change this template use File | Settings | File Templates.
 */

class Typer extends StandardTyperMonad with TyperSyntax with NominalBindingSyntax with Substitution {
  import Terms._
  import Types.{Sel=>TSel, Fun=>FunT, _}
  import Members._
  import TyperMonad.{result, results, fail}
  
  def ofT(tm: Term, pt: Expected[Type]): TyperMonad[Unit] = (
      // Var
      for(Var(x) <- tm;
          tp <- lookup(x);
          _  <- wf(pt);
          _  <- <:<(tp, pt)) yield ()) ++ (
      // Sel
      for(Sel(t, l) <- tm;
          _  <- hasMem(t, l, pt)) yield ()) ++ (
      // App
      for(App(fun, arg) <- tm;
          // check G |- fun : f => t, but don't know f and t --> make new meta-variables
          f  = MetaType("from"); t  = MetaType("to");
          _  <- ofT(fun, Check(FunT(f, t)));
          f  <- !f ; t <- !t;               // force the meta-variables --> must have been unified or something is wrong
          _  <- ofT(arg, Check(f));         // check that the argument has the expected type
          _  <- pt := t) yield ()) ++ (
      // Abs
      for(Fun(ta, \\(x, b)) <- tm;
          _   <- wf(Check(ta));
          tr  = Infer[Type]("tf");
          _   <- fresh(x, tr);
          _   <- assume(x, ta)(ofT(b, tr));
          tr  <- !tr;
          _   <- <:<(FunT(ta, tr), pt);
          _   <- wf(pt)) yield ()) ++ (
      // New
      for(New(tc, \\(x, (args, b))) <- tm; // parsing has already checked tc is a class type
          _   <- wf(Check(tc));
          _   <- fresh(x, pt);
          decls = Infer[Decls]("decls");
          _   <- expands(x, decls);
          decls <- !decls;
          _   <- assume(x, tc)(for(
                    _ <- wfCtorMems(decls, args);
                    _ <- ofT(b, pt)) yield ())) yield ())

  // for nom = Check(cb) check that x is fresh in nom
  // for nom = Infer(_)  record that nom must only be unified with something in which x is fresh
  def fresh[T: ContainsBinders](x: Name, nom: Expected[T]) = result(())


  def hasMem(tgt: Term, l: TermLabel, pt: Expected[Type]): TyperMonad[Unit]
    = memberOf(tgt, Check[Decl[Level, Entity]](TypeDecl(l, pt.toMetaVar(MetaType)))) // XXX TODO: why must we pass MetaType explicitly?

  object Path {
    def unapply(t: Term): Option[Term] = if(t.isPath) Some(t) else None
  }
  def memberOf(tgt: Term, d: Expected[Decl[Level, Entity]]): TyperMonad[Unit] = (
      // Path-has
      for(Path(p) <- tgt;
          t  = MetaType("parent"); decls = MetaScoped[MetaDecls, Decls]("z", MetaDecls("decls"));
          _  <- ofT(p, Check(Refine(t, decls)));
          t  <- !t; \\(z, decls) <- !decls;
          di <- results(decls.decls);
          _  <- d := di subst(z, p)) yield ()) ++ (
      // Term-has
      for(t  <- MetaType("parent"); decls = MetaScoped[MetaDecls, Decls]("z", MetaDecls("decls"));
          _  <- ofT(tgt, Check(Refine(t, decls)));
          t  <- !t; \\(z, decls) <- !decls;
          di <- results(decls.decls);
          _  <- fresh(z, Check(di));
          _  <- d := di) yield ()) ++ (
      // Path-has
      for(d1 <- Infer[Decl[Level, Entity]]("d1"); d2 <- Infer[Decl[Level, Entity]]("d2");
          _  <- memberOf(tgt, d1);
          _  <- memberOf(tgt, d2);
          d1 <- !d1; d2 <- !d2;
          m  <- meet(d1, d2);//.first; // TODO: don't try d2 if d1 leads to successful lookup of member by label 
          _  <- d := m) yield ())

  def meet(d1: Decl[Level, Entity], d2: Decl[Level, Entity]): TyperMonad[Decl[Level, Entity]] = (d1, d2) match {
    case (TypeDecl(l1, cls1), TypeDecl(l2, cls2)) if l1 === l2 => TypeDecl(l1, Intersect(cls1, cls2))
    case (TypeBoundsDecl(l1, TypeBounds(s1, u1)), TypeBoundsDecl(l2, TypeBounds(s2, u2))) if l1 === l2 =>
      TypeBoundsDecl(l1, TypeBounds(Union(s1, s2), Intersect(u1, u2)))
    case _ => results(List(d1, d2))  // order is important
  }

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


trait TyperSyntax extends MetaVariablesNominal with Syntax {
  implicit object MetaType extends MetaVarBuilder[Type, MetaType]("metaTp") {
    def apply(n: String) = new MetaType(n)
  }
  class MetaType(override val name: String) extends Type with MetaVar[Type]

  import Members.Decls
  implicit object MetaDecls extends MetaVarBuilder[Decls, MetaDecls]("metaDecls") {
    def apply(n: String) = new MetaDecls(n)
 }
  class MetaDecls(override val name: String) extends Decls(List()) with MetaVar[Decls] // TODO refactor Decls into abstract superclass and concrete subclass

  implicit def eqEntity(e: Entity): Equality[Entity] = new Equality[Entity] {
    def ===(o: Entity) = (e, o) match {
      case (a: Type, b: Type) => a === b
      case (a: Term, b: Term) => a === b
      case (a: TypeBounds, b: TypeBounds) => a === b
      case _ => false
    }
  }

  implicit def eqType(tp: Type): Equality[Type] = new Equality[Type] { import Types._
    def ===(o: Type) = (tp, o) match {
      case (x: MetaType, _) => x === tp // delegate to MetaType
      case (_, x: MetaType) => x === tp // delegate to MetaType
      case (Sel(tgt, label), Sel(tgto, labelo)) =>  tgt.===(tgto) && label.===(labelo)
      case (Refine(parent, decls), Refine(parento, declso)) => parent.===(parento) && decls.===(declso)
      case (Fun(from, to), Fun(fromo, too)) => from.===(fromo) && to.===(too)
      case (Intersect(tp1, tp2), Intersect(tp1o, tp2o)) => tp1.===(tp1o) && tp2.===(tp2o)
      case (Union(tp1, tp2), Union(tp1o, tp2o)) => tp1o.===(tp1o) && tp2o.===(tp2o)
      case (Top, Top)    => true
      case (Bottom, Bottom) => true
      case _ => false
    }
  }

  implicit def eqTerm(tm: Term): Equality[Term] = new Equality[Term] {
    def ===(o: Term) = tm == o // TODO
  }

  implicit def eqTypeBounds(tb: TypeBounds): Equality[TypeBounds] = new Equality[TypeBounds] {
    def ===(o: TypeBounds) = tb == o // TODO
  }

  implicit def eqLabel[L <: Level](l: Label[L]): Equality[Label[L]] = new Equality[Label[L]] {
    def ===(o: Label[L]) = l == o
  }

  implicit def eqDecl[L <: Level, E <: Entity : ChecksEquality](d: Members.Decl[L, E]): Equality[Members.Decl[L, E]] = new Equality[Members.Decl[L, E]] {
    def ===(od: Members.Decl[L, E]) = d.l === od.l && d.cls === od.cls
  }

  implicit def eqDecls(ds: Members.Decls): Equality[Members.Decls] = new Equality[Members.Decls] {
    def ===(os: Members.Decls) = (ds.decls.length == os.decls.length) && (
            ds.decls.forall{d =>
              os.decls.exists{od => d === od}})
  }

  implicit def eqDef[E <: Entity : ChecksEquality](d: Members.Def[E]): Equality[Members.Def[E]] = new Equality[Members.Def[E]] {
    def ===(od: Members.Def[E]) = d.l === od.l && d.rhs === od.rhs
  }

  implicit def eqDefs(ds: Members.ValDefs): Equality[Members.ValDefs] = new Equality[Members.ValDefs] {
    def ===(os: Members.ValDefs) = (ds.defs.length == os.defs.length) && (
            ds.defs.forall{d =>
              os.defs.exists{od => d === od }})
  }

}