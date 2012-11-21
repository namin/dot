package dot

trait DotTyper extends StandardTyperMonad with DotTyperSyntax with DotNominalSyntax with DotSubstitution {
  override type State = Int
  override val initState = 0
  def tag: TyperMonad[Int] = TyperMonad{from =>
    from.mapStateTo({state => state + 1}, {state => TyperSuccess(state)})
  }

  def freshName(n: String): TyperMonad[Name] = for (s <- tag) yield (Name(n+"$tag$"+s))

  import Terms._
  import Types._
  import Members._
  import TyperMonad._

  def typecheck(tm: Term): Result[Type] = {
    val r = (for(
      ein <- Infer[Type]("in");
      _ <- ofT(tm, ein);
      in <- !ein) yield in).findAll
    assert(r.length==1, "typecheck result is not unique: "+r)
    r.head
  }

  def ofT(tm: Term, pt: Expected[Type]): TyperMonad[Unit] = {
    debug("-------------------------")
    debug("type of " + tm + ":" + pt)
    tm match {
      case Var(x) => for(
        r <- lookup(x);
        _ <- pt := r) yield ()
      case Sel(o, l) => for(
        tp <- memValue(o, l);
        _ <- pt := tp) yield ()
      case Msel(o, m, a) => for(
        ArrowType(s, u) <- memMethod(o, m);
        _ <- pt := u;
        ta <- Infer[Type]("argTp");
        _ <- ofT(a, ta);
        ta <- !ta;
        _ <- sub(ta, s)) yield ()
      case New(tc, \\(y, (args, b))) => for(
        _ <- wfe(tc);
        ds <- expand(y, tc);
        _ <- assume(y, tc){for(
          _ <- wfCtorMems(ds, args);
          _ <- ofT(b, pt);
          tp <- !pt;
          if tp fresh(y)) yield ()}) yield ()
    }
  }

  def wfCtorMems(ds: Dcls, args: Defs): TyperMonad[Unit] = ds match {
    case BottomDecls =>
      fail("bottom expansion for constructor type")
    case Decls(ds) if !args.defs.forall{d1 => ds.exists{d2 => d1.l==d2.l}} =>
      fail("initialized label is undeclared")
    case Decls(ds) => forall(ds) {
      case TypeDecl(l, TypeBounds(s, u)) => sub(s, u)
      case ValueDecl(l, u) => for(
        ValueDef(_, v) <- exactlyOne(args.defs.find(d => d.l===l), "uninitialized value for label " + l);
        etv <- Infer[Type]("valTp");
        _ <- ofT(v, etv);
        tv <- !etv;
        _ <- sub(tv, u)) yield ()
      case MethodDecl(l, ArrowType(s, u)) => for(
        MethodDef(_, Method(\\(x, b))) <- exactlyOne(args.defs.find(d => d.l===l), "uninitialized method for label " + l);
        etb <- Infer[Type]("bodyTp");
        _ <- assume(x, s)(ofT(b, etb));
        tb <- !etb;
        _ <- sub(tb, u)) yield ()
    }
  }

  def mergeDecl[L <: Level, E <: Entity](funlo: (Type, Type) => Type, funhi: (Type, Type) => Type)(
    d1: Decl[L,E], d2: Decl[L,E]): Dcl = (d1, d2) match {
      case (TypeDecl(l1, TypeBounds(s1, u1)), TypeDecl(l2, TypeBounds(s2, u2))) if l1===l2 =>
        TypeDecl(l1, TypeBounds(funlo(s1, s2), funhi(u1, u2)))
      case (MethodDecl(l1, ArrowType(s1, u1)), MethodDecl(l2, ArrowType(s2, u2))) if l1===l2 =>
        MethodDecl(l1, ArrowType(funlo(s1, s2), funhi(u1, u2)))
      case (ValueDecl(l1, u1), ValueDecl(l2, u2)) if l1===l2 =>
        ValueDecl(l1, funhi(u1, u2))
    }
  def intersect(a: Type, b: Type): Type = (a, b) match {
    case (Bottom, other) => Bottom
    case (other, Bottom) => Bottom
    case (Top, other) => other
    case (other, Top) => other
    case (a, b) => Intersect(a, b)
  }
  def union(a: Type, b: Type): Type = (a, b) match {
    case (Bottom, other) => other
    case (other, Bottom) => other
    case (Top, other) => Top
    case (other, Top) => Top
    case (a, b) => Union(a, b)
  }
  def intersectDecl = mergeDecl(union, intersect) _
  def unionDecl = mergeDecl(intersect, union) _
  //  intersection of declaration sets
  def meet(ds1: Dcls, ds2: Dcls): Dcls = (ds1, ds2) match {
    case (BottomDecls, _) => BottomDecls
    case (_, BottomDecls) => BottomDecls
    case (Decls(ds1), Decls(ds2)) => Decls(
      ds1.flatMap{d1 => ds2.find{d2 => d1.l===d2.l}.map{d2 => intersectDecl(d1, d2)}} ++
      ds1.filterNot{d1 => ds2.exists{d2 => d1.l===d2.l}} ++
      ds2.filterNot{d2 => ds1.exists{d1 => d1.l===d2.l}})
  }
  // union of declaration sets
  def join(ds1: Dcls, ds2: Dcls): Dcls = (ds1, ds2) match {
    case (BottomDecls, other) => other
    case (other, BottomDecls) => other
    case (Decls(ds1), Decls(ds2)) => Decls(
      ds1.flatMap{d1 => ds2.find{d2 => d1.l===d2.l}.map{d2 => unionDecl(d1, d2)}})
  }

  def memValue(o: Term, l: ValueLabel): TyperMonad[Type] = for(
    tp <- Infer[Type]("memValTp").toMetaVar(MetaType);
    _ <- mem(o, ValueDecl(l, tp));
    tp <- !tp) yield tp

  def memMethod(o: Term, m: MethodLabel): TyperMonad[ArrowType] = for(
    lo <- Infer[Type]("memMetTp").toMetaVar(MetaType);
    hi <- Infer[Type]("memMetTp").toMetaVar(MetaType);
    _ <- mem(o, MethodDecl(m, ArrowType(lo, hi)));
    lo <- !lo;
    hi <- !hi) yield ArrowType(lo, hi)

  def memType(o: Term, l: TypeLabel): TyperMonad[TypeBounds] = for(
    lo <- Infer[Type]("memTypTp").toMetaVar(MetaType);
    hi <- Infer[Type]("memTypTp").toMetaVar(MetaType);
    _ <- mem(o, TypeDecl(l, TypeBounds(lo, hi)));
    lo <- !lo;
    hi <- !hi) yield TypeBounds(lo, hi)

  def mem(tm: Term, d: Dcl): TyperMonad[Unit] = {
    debug("mem? " + tm + " : " + d)
    val r = for(
      etp <- Infer[Type]("memObjTp");
      _ <- ofT(tm, etp);
      tp <- !etp;
      z <- freshName("z");
      ds <- expand(z, tp);
      _ <- debug("expanded to " + ds);
      di <- exactlyOne(ds.findByLabel(d.l), "undeclared label " + d.l);
      _ <- debug("found decl " + di)) yield (z, di)

    if (tm.isPath) {
      debug("mem-path");
      for ((z, di) <- r;
           _ <- check(entityIsSubstable(di.cls).subst(z, tm)===d.cls)) yield ()
    } else {
      debug("mem-term")
      for ((z, di) <- r;
           _ <- some(List((for (_ <- check(entityHasBinders(di.cls).fresh(z));
                                _ <- debug("mem-term restriction ok");
                                _ <- check(di.cls===d.cls)) yield ())),
                     "mem-term restriction fails for " + z + " in " + di)) yield ()
    }
  }

  def expand(x: Name, tp: Type): TyperMonad[Dcls] = {
    debug("expand_" + x + " of " + tp)
    tp match {
      case Refine(parent, \\(z, ds)) =>
        for (dsp <- expand(x, parent))
        yield meet(dsp, ds swap(z, x))
      case Intersect(a, b) =>
        for (dsa <- expand(x, a);
             dsb <- expand(x, b))
        yield meet(dsa, dsb)
      case Union(a, b) =>
        for (dsa <- expand(x, a);
             dsb <- expand(x, b))
        yield join(dsa, dsb)
      case Tsel(p, l) =>
        for (TypeBounds(s, u) <- memType(p, l);
             dsu <- expand(x, u))
        yield dsu
      case Top => Decls(List())
      case Bottom => BottomDecls
    }
  }

  def sub(tp1: Type, tp2: Type): TyperMonad[Unit] = some(List(
    /*refl*/    (for(_ <- check(tp1===tp2); _ <- wfe(tp1))                                                   yield()),
    /*<:-top*/  (for(_ <- check(tp2===Top); _ <- wfe(tp1))                                                   yield()),
    /*bot-<:*/  (for(_ <- check(tp1===Bottom); _ <- wfe(tp2))                                                yield()),
    /*<:-and*/  (for(Intersect(a, b) <- tp2; _ <- sub(tp1, a); _ <- sub(tp1, b))                             yield()),
    /*or-<:*/   (for(Union(a, b) <- tp1; _ <- sub(a, tp2); _ <- sub(b, tp2))                                 yield()),
    /*and1-<:*/ (for(Intersect(a, b) <- tp1; _ <- sub(a, tp2); _ <- wfe(b))                                  yield()),
    /*and2-<:*/ (for(Intersect(a, b) <- tp1; _ <- sub(b, tp2); _ <- wfe(a))                                  yield()),
    /*<:-or1*/  (for(Union(a, b) <- tp2; _ <- sub(tp1, a); _ <- wfe(b))                                      yield()),
    /*<:-or2*/  (for(Union(a, b) <- tp2; _ <- sub(tp1, b); _ <- wfe(a))                                      yield()),
    /*<:-tsel*/ (for(Tsel(p, l) <- tp2; TypeBounds(s, u) <- memType(p, l); _ <- sub(s, u); _ <- sub(tp1, s)) yield()),
    /*tsel-<:*/ (for(Tsel(p, l) <- tp1; TypeBounds(s, u) <- memType(p, l); _ <- sub(s, u); _ <- sub(u, tp2)) yield()),
    /*rfn-<:*/  (for(Refine(parent, \\(z, ds)) <- tp1; _ <- wfe(tp1); _ <- sub(parent, tp2))                 yield()),
    /*<:-rfn*/  (for(Refine(parent, \\(z, ds)) <- tp2; _ <- wfe(tp2); _ <- sub(tp1, parent);
                     ds1 <- expand(z, tp1);
                     _ <- assume(z, tp1){
                       forall(ds.decls){d2 => for(d1 <- exactlyOne(ds1.findByLabel(d2.l));
                                                  _ <- subDecl(d1, d2)) yield()}})                           yield())),
    err=tp1 + " is not a subtype of " + tp2)

  def subDecl[L <: Level, E <: Entity](d1: Decl[L,E], d2: Decl[L,E]): TyperMonad[Unit] = (d1, d2) match {
    case (TypeDecl(l1, TypeBounds(s1, u1)), TypeDecl(l2, TypeBounds(s2, u2))) if l1===l2 =>
      for (_ <- sub(s2, s1); _ <- sub(u1, u2)) yield()
    case (MethodDecl(l1, ArrowType(s1, u1)), MethodDecl(l2, ArrowType(s2, u2))) if l1===l2 =>
      for (_ <- sub(s2, s1); _ <- sub(u1, u2)) yield()
    case (ValueDecl(l1, u1), ValueDecl(l2, u2)) if l1===l2 =>
      for (_ <- sub(u1, u2)) yield()
  }

  def wf(tp: Type): TyperMonad[Unit] = tp match {
    case Top => ()
    case Bottom => ()
    case Refine(parent, \\(z, Decls(ds))) =>
      for (_ <- wf(parent);
           _ <- assume(z, tp){forall(ds) { wfDecl(_) }})
      yield ()
    case Intersect(a, b) =>
      for (_ <- wf(a);
           _ <- wf(b))
      yield ()
    case Union(a, b) =>
      for (_ <- wf(a);
           _ <- wf(b))
      yield ()
    case Tsel(p, l) => some(List(
      (for (TypeBounds(Bottom, u) <- memType(p, l))
       yield ()),
      (for (TypeBounds(s, u) <- memType(p, l);
            _ <- wf(s);
            _ <- wf(u))
       yield ())))
  }

  def wfDecl(d: Dcl): TyperMonad[Unit] = d match {
    case TypeDecl(l, TypeBounds(s, u)) => for(
      _ <- wf(s); _ <- wf(u)) yield ()
    case MethodDecl(l, ArrowType(s, u)) => for(
      _ <- wf(s); _ <- wf(u)) yield ()
    case ValueDecl(l, u) => for(
                  _ <- wf(u)) yield ()
  }

  def wfe(tp: Type): TyperMonad[Unit] = for(
    _ <- wf(tp);
    z <- freshName("z");
    _ <- expand(z, tp)) yield ()
}

trait DotTyperSyntax extends MetaVariablesNominal with DotSyntax {
  // TODO: is there a point in making it implicit?
  object MetaType extends MetaVarBuilder[Type, MetaType]("metaTp") {
    def apply(n: String) = new MetaType(n)
  }
  class MetaType(override val name: String) extends Type with MetaVar[Type]

  implicit def eqEntity(e1: Entity): Equality[Entity] = new Equality[Entity] {
    def ===(e2: Entity) = (e1, e2) match {
      case (a: TypeBounds, b: TypeBounds) => a === b
      case (a: Type, b: Type) => a === b
      case (a: Term, b: Term) => a === b
      case (a: ArrowType, b: ArrowType) => a === b
      case (a: Method, b: Method) => a === b
      case _ => false
    }
  }

  implicit def eqType(tp1: Type): Equality[Type] = new Equality[Type] {
    import Types._
    def ===(tp2: Type) = (tp1, tp2) match {
      case (x1: MetaType, _) => x1===tp2
      case (_, x2: MetaType) => x2===tp1
      case (Tsel(o1, l1), Tsel(o2, l2)) => o1===o2 && l1===l2
      case (Refine(parent1, decls1), Refine(parent2, decls2)) => parent1===parent2 && decls1===decls2
      case (Intersect(a1, b1), Intersect(a2, b2)) => a1===a2 && b1===b2
      case (Union(a1, b1), Union(a2, b2)) => a1===a2 && b1===b2
      case (Top, Top) => true
      case (Bottom, Bottom) => true
      case _ => false
    }
  }

  implicit def eqPath(tm1: Term): Equality[Term] = new Equality[Term] {
    import Terms._
    def ===(tm2: Term) = (tm1, tm2) match {
      case (Var(n1), Var(n2)) => n1===n2
      case (Sel(o1, l1), Sel(o2, l2)) => o1===o2 && l1===l2
      case _ => assert(tm1.isPath && tm2.isPath); false
    }
  }

  implicit def eqLabel[L <: Level](l1: Label[L]): Equality[Label[L]] = new Equality[Label[L]] {
    def ===(l2: Label[L]) = l1 == l2
  }

  implicit def eqTypePair[L <: Level](p1: TypePair[L]): Equality[TypePair[L]] = new Equality[TypePair[L]] {
    def ===(p2: TypePair[L]) = p1.lo===p2.lo && p1.hi===p2.hi
  }

  implicit def eqDecl[L <: Level, E <: Entity : ChecksEquality](d1: Members.Decl[L, E]): Equality[Members.Decl[L, E]] = new Equality[Members.Decl[L, E]] {
    def ===(d2: Members.Decl[L, E]) = d1.l===d2.l && d1.cls==d2.cls
  }

  def eqListAsSet[A : ChecksEquality](s1: List[A]): Equality[List[A]] = new Equality[List[A]] {
    def ===(s2: List[A]) =
      s1.length == s2.length && s1.forall{x1 => s2.exists{x2 => x1 === x2}}
  }

  implicit def eqDcls(ds1: Members.Dcls): Equality[Members.Dcls] = new Equality[Members.Dcls] {
    def ===(ds2: Members.Dcls) = (ds1, ds2) match {
      case (Members.Decls(s1), Members.Decls(s2)) => eqListAsSet(s1)===s2
      case _ => false
    }
  }
}
