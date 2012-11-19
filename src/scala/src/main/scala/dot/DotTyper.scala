package dot

trait Constraints extends StandardTyperMonad {
  override type State = Set[Constraint]
  override val initState = Set[Constraint]()

  def addConstraint(c: Constraint): TyperMonad[Unit] = TyperMonad{from =>
    from.mapStateTo({state => state + c}, {state => Success(())})
  }

  implicit def constraintExpected(tp1: Expected[Type]) = new {
    def <:<(tp2: Expected[Type]): Constraint = new SubtypeConstraint(tp1, tp2)
  }

  trait Constraint
  case class SubtypeConstraint(tv1: Expected[Type], tv2: Expected[Type]) extends Constraint
}

trait DotTyper extends StandardTyperMonad with Constraints with DotTyperSyntax with DotNominalSyntax with DotSubstitution {
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
	  _ <- ofT(b, pt)) yield ()}) yield ()
    }
  }

  def wfCtorMems(ds: Dcls, args: Defs): TyperMonad[Unit] = ds match {
    case BottomDecls => fail("bottom expansion for constructor type")
    case Decls(ds) => forall(ds) {
      case TypeDecl(l, TypeBounds(s, u)) => sub(s, u)
      // TODO...
    }
  }

  def expand(x: Name, tp: Type): TyperMonad[Dcls] = tp match {
    case Top => Decls(List())
    case Bottom => BottomDecls
    // TODO
    case Refine(parent, \\(z, decls)) if parent===Top => decls swap(z, x)
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
