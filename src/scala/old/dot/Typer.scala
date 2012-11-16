package scala.dot

import collection.immutable.{Map, HashMap, Set}

import scala.util.binding.frescala.AbstractBindingSyntax
import scala.util.Equalities

/**
 * Created by IntelliJ IDEA.
 * User: adriaan
 * Date: Oct 29, 2009
 * Time: 10:46:51 AM
 * To change this template use File | Settings | File Templates.
 */
trait Constraints extends StandardTyperMonad with  TyperSyntax {
  type State = Set[Constraint]
  val initState = Set()

  def addConstraint(c: Constraint): TyperMonad[()] =

  implicit def constrainExpected(tp1: Expected[Type]) = new {def <:<(tp2: Expected[Type]): Constraint = new SubtypeConstraint(tp1, tp2) }

  class Constraint
  case class SubtypeConstraint(tv1: Expected[Type], tv2: Expected[Type]) extends Constraint
}

class Typer extends StandardTyperMonad with Constraints with TyperSyntax with NominalBindingSyntax with Substitution {
  import Terms._
  import Types.{Sel=>TSel, Fun=>FunT, _}
  import Members._
  import TyperMonad._


  def ofT(tm: Term, pt: Expected[Type]): TyperMonad[Unit] = tm match {
    // Var
    case Var(x) => for(
        _  <- pt := lookup(x)) yield ()
    // Sel
    case Sel(t, l) => for(
        _  <- hasMem(t, l, pt)) yield ()
    // App
    case App(fun, arg) => for(
        f  <- Infer[Type]("from");
        _  <- ofT(fun, Check(FunT(f.toMetaVar(MetaType), pt.toMetaVar(MetaType))));
        _  <- ofT(arg, f)) yield ()
    // Abs
    case Fun(ta, \\(x, b)) => for(
        _   <- wf(Check(ta));
        tr  = Infer[Type]("tr");
        _   <- assume(x, ta)(ofT(b, tr));
        tr  <- !tr;
        _   <- fresh(x, tr);
        _   <- pt := FunT(ta, tr.toMetaVar(MetaType));
        _   <- wf(pt)) yield ()
    // New
    case New(tc, \\(x, (args, b))) => for( // parsing has already checked tc is a class type
        _   <- wf(Check(tc));
        _   <- assume(x, tc){for(
                  decls <- expand(x, tc);
                  _     <- wfCtorMems(decls, args);
                  _     <- fresh(x, pt);
                  _     <- ofT(b, pt)) yield ()}) yield ()
  }


  // decls = L_i: S_i..U_i, l_j : V_j
  // args = l_j = v_j
  // check: G |- S_i <: U_i
  //        G |- v_j : V_j
  def wfCtorMems(ds: Decls, args: ValDefs): TyperMonad[Unit]
    = forall(ds.decls){
        case TypeBoundsDecl(l, TypeBounds(s, u)) =>
          <:<(Check(s), Check(u))
        case TypeDecl(l, tp) =>
          for(a <- exactlyOne(args.defs find {_.l === l});
              _ <- ofT(a.rhs, tp)) yield ()
      }

  // for nom = Check(cb) check that x is fresh in nom
  // for nom = Infer(_)  record that nom must only be unified with something in which x is fresh
  def fresh[T: ContainsBinders](x: Name, nom: Expected[T]) = result(())   // TODO

  def hasMem(tgt: Term, l: TermLabel, pt: Expected[Type]): TyperMonad[Unit]
    = memberOf(tgt, Check[Dcl](TypeDecl(l, pt.toMetaVar(MetaType)))) // XXX TODO: why must we pass MetaType explicitly?

  def memberOf(tgt: Term, d: Expected[Dcl]): TyperMonad[Unit] = (
      // Path-has
      for(Path(p) <- tgt;
          decls = MetaScoped[MetaDecls, Decls]("z", MetaDecls("decls") containingLike d);
          _  <- ofT(p, Check(Refine(MetaType("_T"), decls)));
          \\(z, decls) <- !decls;
          di <- results(decls.decls);
          _  <- d := di subst(z, p)) yield ()) ++ (
      // Term-has
      for(decls <- MetaScoped[MetaDecls, Decls]("z", MetaDecls("decls") containingLike d);
          _  <- ofT(tgt, Check(Refine(MetaType("_T"), decls)));
          \\(z, decls) <- !decls;
          di <- results(decls.decls);
          _  <- fresh(z, Check(di));
          _  <- d := di) yield ()) ++ (
      // And-has
      for(d1 <- Infer[Dcl]("d1"); d2 <- Infer[Dcl]("d2");
          _  <- memberOf(tgt, d1);
          _  <- memberOf(tgt, d2);
          d1 <- !d1; d2 <- !d2;
          m  <- results(merge(d1, d2));//.first; // TODO: don't try d2 if d1 leads to successful lookup of member by label
          _  <- d := m) yield ())

  // TODO: cleaner verion of merge&meet
  def merge(d1: Dcl, d2: Dcl): List[Dcl] = (d1, d2) match {
    case (TypeDecl(l1, cls1), TypeDecl(l2, cls2)) if l1 === l2 => List(TypeDecl(l1, Intersect(cls1, cls2)))
    case (TypeBoundsDecl(l1, TypeBounds(s1, u1)), TypeBoundsDecl(l2, TypeBounds(s2, u2))) if l1 === l2 =>
      List(TypeBoundsDecl(l1, TypeBounds(Union(s1, s2), Intersect(u1, u2))))
    case _ => List(d1, d2)  // order is important
  }

  def meet(ds1: Decls, ds2: Decls): Decls = Decls(
     ds1.decls.map{d1 => (ds2.decls.find{d2 => d1.l === d2.l} map {d12 => merge(d1, d12).head}) getOrElse d1} ++
     ds2.decls.filterNot{d2 => ds1.decls.exists{d1 => d1.l === d2.l}}
    )

  def classTypeMemberOf(p: Term, lc: TypeLabel): TyperMonad[Type] =
    force(MetaType("hi"))(t => memberOf(p, Check(TypeBoundsDecl(lc, TypeBounds(Bottom, t)))))

  def expand(x: Name, tp: Type): TyperMonad[Decls] = tp match {
    case Refine(ClassType(tc), \\(z, decls)) =>       // Rfn-expands
      for(decls2 <- expand(z, tc))
        yield meet(decls, decls2) swap(z, x)
    case TSel(Path(p), ClassLabel(lc)) =>             // Tsel-expands
      for(tp <- classTypeMemberOf(p, lc);
          res <- expand(x, tp))
         yield res
    case Top =>                                       // Top-expands
      Decls(List())
    case Intersect(ClassType(tc1), ClassType(tc2)) => // Intersect-expands
      for(ds1 <- expand(x, tc1);
          ds2 <- expand(x, tc2))
          yield meet(ds1, ds2)
  }

  // for pt = Check(tp2) check that tp1 is a subtype of pt
  // for pt = Infer(_)   subsume tp1 to tp2 so that pt can be unified with tp2
  def <:<(tp1: Expected[Type], tp2: Expected[Type]): TyperMonad[Unit] =
      if(tp1.unknown || tp2.unknown) {
        addConstraint(tp1 <:< tp2)
      } else (
      // Refl
      for(_  <- tp1 := tp2.toMetaVar(MetaType)) yield ()) ++ (
      // <:-FunT
      for(s1 <- Infer[Type]("S");  t1 <- Infer[Type]("T");
          s2 <- Infer[Type]("S'"); t2 <- Infer[Type]("T'");
          _  <- tp1 := FunT(t1.toMetaVar(MetaType), t2.toMetaVar(MetaType));
          _  <- tp2 := FunT(s1.toMetaVar(MetaType), s2.toMetaVar(MetaType));
          _  <- <:<(t1, s1);
          _  <- <:<(s2, t2)) yield ()) ++ (
      // Rfn-<:
      for(t  <- Infer[Type]("T"); ds <- MetaScoped[MetaDecls, Decls]("z", MetaDecls("decls"));
          _  <- tp1 := Refine(t.toMetaVar(MetaType), ds);
          _  <- <:<(t, tp2)) yield ()) ++ (
      // <:-Rfn
          // TODO
      // <:-Tsel
          // TODO
      // Tsel-<:
          // TODO
      // <:-Intersect
      for(t1 <- Infer[Type]("T1"); t2 <- Infer[Type]("T2");
          _  <- tp2 := Intersect(t1.toMetaVar(MetaType), t2.toMetaVar(MetaType));
          _  <- <:<(tp1, t1);
          _  <- <:<(tp1, t2)) yield ()) ++ (
      // Intersect-<:-1
      for(t1 <- Infer[Type]("T1"); t2 <- Infer[Type]("T2");
          _  <- tp1 := Intersect(t1.toMetaVar(MetaType), t2.toMetaVar(MetaType));
          _  <- <:<(t1, tp2)) yield ()) ++ (
      // Intersect-<:-2
      for(t1 <- Infer[Type]("T1"); t2 <- Infer[Type]("T2");
          _  <- tp1 := Intersect(t1.toMetaVar(MetaType), t2.toMetaVar(MetaType));
          _  <- <:<(t2, tp2)) yield ()) ++ (
      // <:-Union-1
      for(t1 <- Infer[Type]("T1"); t2 <- Infer[Type]("T2");
          _  <- tp2 := Union(t1.toMetaVar(MetaType), t2.toMetaVar(MetaType));
          _  <- <:<(tp1, t1)) yield ()) ++ (
      // <:-Union-2
      for(t1 <- Infer[Type]("T1"); t2 <- Infer[Type]("T2");
          _  <- tp2 := Union(t1.toMetaVar(MetaType), t2.toMetaVar(MetaType));
          _  <- <:<(tp1, t2)) yield ()) ++ (
      // Union-<:
      for(t1 <- Infer[Type]("T1"); t2 <- Infer[Type]("T2");
          _  <- tp1 := Union(t1.toMetaVar(MetaType), t2.toMetaVar(MetaType));
          _  <- <:<(t1, tp2);
          _  <- <:<(t2, tp2)) yield ()) ++ (
      // <:-Top
      for(_ <- tp2 := Top) yield ()) ++ (
      // Bottom-<:
      for(_ <- tp1 := Bottom) yield ())


  def subDecl(d1: Expected[Dcl], d2: Expected[Dcl]): TyperMonad[Unit] = (
      for(l  <- MetaTypeLabel("L");
          s1 <- Infer[Type]("S");  t1 <- Infer[Type]("T");
          s2 <- Infer[Type]("S'"); t2 <- Infer[Type]("T'");
          _  <- d1 := TypeBoundsDecl(l, TypeBounds(s1.toMetaVar(MetaType), t1.toMetaVar(MetaType)));
          _  <- d2 := TypeBoundsDecl(l, TypeBounds(s2.toMetaVar(MetaType), t2.toMetaVar(MetaType)));
          _  <- <:<(s2, s1);
          _  <- <:<(t1, t2)) yield ()) ++ (
      for(l  <- MetaTermLabel("l");
          t1 <- Infer[Type]("T");
          t2 <- Infer[Type]("T'");
          _  <- d1 := TypeDecl(l, t1.toMetaVar(MetaType));
          _  <- d2 := TypeDecl(l, t2.toMetaVar(MetaType));
          _  <- <:<(t1, t2)) yield ())

  // for pt = Check(tp2) check that tp is well-formed
  // for pt = Infer(_)   record that pt must only be unified with a well-formed type
  def wf(pt: Expected[Type]): TyperMonad[Unit]
    = result(()) // TODO
}


trait TyperSyntax extends MetaVariablesNominal with Syntax {
  object Path {
    def unapply(t: Term): Option[Term] = if(t.isPath) Some(t) else None
  }

  object ClassType {
    def unapply(tp: Type): Option[Type] = if(tp.isConcrete) Some(tp) else None
  }

  object ClassLabel {
    def unapply(l: TypeLabel): Option[TypeLabel] = if(l.isConcrete) Some(l) else None
  }

  implicit object MetaTypeLabel extends MetaVarBuilder[TypeLabel, MetaTypeLabel]("metaTpL") {
    def apply(n: String) = new MetaTypeLabel(n, false) //TODO: shouldn't hardwire false here?
  }
  class MetaTypeLabel(override val name: String, c: Boolean) extends TypeLabel(name, c) with MetaVar[TypeLabel]

  implicit object MetaTermLabel extends MetaVarBuilder[TermLabel, MetaTermLabel]("metaTmL") {
    def apply(n: String) = new MetaTermLabel(n)
  }
  class MetaTermLabel(override val name: String) extends TermLabel(name) with MetaVar[TermLabel]

  implicit object MetaType extends MetaVarBuilder[Type, MetaType]("metaTp") {
    def apply(n: String) = new MetaType(n)
  }
  class MetaType(override val name: String) extends Type with MetaVar[Type]

  import Members.Decls
  implicit object MetaDecls extends MetaVarBuilder[Decls, MetaDecls]("metaDecls") {
    def apply(n: String) = new MetaDecls(n)
 }
  class MetaDecls(override val name: String) extends Decls(List()) with MetaVar[Decls] {// TODO refactor Decls into abstract superclass and concrete subclass
    def containingLike(d: Expected[Members.Dcl]): this.type = this // TODO: metavar that only unifies with set containing a declaration with label d.l
  }

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