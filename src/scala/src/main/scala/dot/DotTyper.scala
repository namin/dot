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

trait Typer extends StandardTyperMonad with Constraints with DotTyperSyntax with DotNominalSyntax with DotSubstitution {
  import Terms._
  import Types._
  import Members._
  import TyperMonad._
}

trait DotTyperSyntax extends MetaVariablesNominal with DotSyntax {
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
      case (Tsel(o1, l1), Tsel(o2, l2)) => o1===o2 && l1===l2
      case (Refine(parent1, decls1), Refine(parent2, decls2)) => parent1===parent2 && decls1===decls2
      case (Intersect(a1, b1), Intersect(a2, b2)) => a1===a2 && b1===b2
      case (Union(a1, b1), Union(a2, b2)) => a1===a2 && b1===b2
      case (Top,Top) => true
      case (Bottom,Bottom) => true
      case _ => false
    }
  }

  implicit def eqTerm(tm1: Term): Equality[Term] = new Equality[Term] {
    import Terms._
    def ===(tm2: Term) = (tm1, tm2) match {
      case (Var(n1), Var(n2)) => n1===n2
      case (Sel(o1, l1), Sel(o2, l2)) => o1===o2 && l1===l2
      case (Msel(o1, m1, a1), Msel(o2, m2, a2)) => o1===o2 && m1===m2 && a1===a2
      case (New(tp1, as1), New(tp2, as2)) => tp1===tp2 && as1==as2
      case _ => false
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

  implicit def eqDef[L <: Level, E <: Entity : ChecksEquality](d1: Members.Def[L, E]): Equality[Members.Def[L, E]] = new Equality[Members.Def[L, E]] {
    def ===(d2: Members.Def[L, E]) = d1.l===d2.l && d1.rhs==d2.rhs
  }

  def eqListAsSet[A : ChecksEquality](s1: List[A]): Equality[List[A]] = new Equality[List[A]] {
    def ===(s2: List[A]) =
      s1.length == s2.length && s1.forall{x1 => s2.exists{x2 => x1 === x2}}
  }

  implicit def eqDecls(ds1: Members.Decls): Equality[Members.Decls] = new Equality[Members.Decls] {
    def ===(ds2: Members.Decls) = eqListAsSet(ds1.decls)===ds2.decls
  }

  implicit def eqDefs(ds1: Members.Defs): Equality[Members.Defs] = new Equality[Members.Defs] {
    def ===(ds2: Members.Defs) = eqListAsSet(ds1.defs)===ds2.defs
  }
}
