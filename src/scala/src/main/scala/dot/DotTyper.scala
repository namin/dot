package dot

trait DotTyper extends StandardTyperMonad with DotTyperSyntax with DotNominalSyntax with DotSubstitution {
  override type State = Int
  override val initState = 0
  def tag: TyperMonad[Int] = TyperMonad{from =>
    from.mapStateTo({state => state + 1}, {state => Success(state)})
  }
  def freshName(n: String): TyperMonad[Name] = for (s <- tag) yield (Name(n+"$tag$"+s))

  import Terms._
  import Types._
  import Members._
  import TyperMonad._

  override val debugMode = true

  def typecheck(tm: Term): Result[Type] = {
    val r = (for(
      ein <- Infer[Type]("in");
      _ <- ofT(tm, ein);
      in <- !ein) yield in).findAll
    assert(r.length==1)
    r.head
  }

  def ofT(tm: Term, pt: Expected[Type]): TyperMonad[Unit] = {
    debug("type of " + tm + ":" + pt)
    tm match {
      case Var(x) => for(
	r <- lookup(x);
	_ <- pt := r) yield ()
      //case Sel(o, l) => TODO
      //case Msel(o, m, a) => TODO
      case New(tc, \\(x, (args, b))) => for(
	// TODO: complete stub
	_ <- assume(x, tc){for(
	  ds <- expand(x, tc);
	  _ <- wfCtorMems(ds, args);
	  _ <- ofT(b, pt);
	  tp <- !pt;
	  if tp fresh(x)) yield ()}) yield ()
    }
  }

  def wfCtorMems(ds: Dcls, args: Defs): TyperMonad[Unit] = ds match {
    case BottomDecls => fail("bottom expansion for constructor type")
    case Decls(ds) => forall(ds) {
      case TypeDecl(l, TypeBounds(s, u)) => sub(s, u)
      // TODO...
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
  def intersectDecl = mergeDecl(Union, Intersect) _
  def unionDecl = mergeDecl(Intersect, Union) _
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

  def mem(tm: Term, d: Dcl): TyperMonad[Unit] = for(
    etp <- Infer[Type]("memtp");
    _ <- ofT(tm, etp);
    tp <- !etp;
    z <- freshName("z");
    ds <- expand(z, tp);
    Some(di) = ds.findByLabel(d.l);
    if ((entityHasBinders(di.cls).fresh(z) && di.cls===d.cls) ||
	(tm.isPath && entityIsSubstable(di.cls).subst(z, tm)===d.cls))) yield ()


  def expand(x: Name, tp: Type): TyperMonad[Dcls] = tp match {
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
    /*case Tsel(p, l) => // TODO */
    case Top => Decls(List())
    case Bottom => BottomDecls
  }

  def sub(tp1: Type, tp2: Type): TyperMonad[Unit] = {
    if (tp2 === Top) ()
    else if (tp1 === Bottom) ()
    else fail(tp1 + " is not a subtype of " + tp2)
    // TODO
  }
}

trait DotTyperSyntax extends MetaVariablesNominal with DotSyntax {
  implicit object MetaType extends MetaVarBuilder[Type, MetaType]("metaTp") {
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
    def ===(p2: TypePair[L]) = p1.lo==p2.lo && p1.hi==p2.hi
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
