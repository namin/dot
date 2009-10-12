package scala.dot
import scala.util.binding.frescala
import frescala.AbstractBindingSyntax

trait Syntax extends AbstractBindingSyntax {
  abstract class Level {
    type Classifies <: Level
  }
  object Levels {
    abstract class TypeBounds extends Level { type Classifies = Type }
    abstract class Type extends Level { type Classifies = Term }
    abstract class ClassType extends Type
    abstract class AbstractType extends Type    
    abstract class Term extends Level { type Classifies = Nothing }
  }  

  object Label {
    trait IsConcrete[T <: Level] {val result: Boolean}
    implicit object concreteClassType extends IsConcrete[Levels.ClassType] { val result = true}
    def notConcrete[T <: Level] = new IsConcrete[T] { val result = false}
    def implicitlyDefault[T](default: T)(implicit v: T=default):T = v

    def isConcrete[T <: Level] = implicitlyDefault[IsConcrete[T]](notConcrete).result

    trait LabelBuilder[T <: Level] extends (String => Label[T])
    def defaultLabelBuilder[T <: Level] = new LabelBuilder[T]{def apply(n: String) = new Label(n)}
    implicit object concreteClassTypeLabelBuilder extends LabelBuilder[Levels.ClassType] { 
      val labels = new scala.collection.mutable.HashMap[String, Label[Levels.ClassType]]
      def apply(n: String) = {
        assert(!labels.isDefinedAt(n))
        labels cached (n, new Label[Levels.ClassType](n))
      }
    }

    def apply[T <: Level](name: String)(implicit b: LabelBuilder[T] = defaultLabelBuilder[T]) = b(name)
  }
  
  class Label[+T <: Level](name: String) {
    def isConcrete = Label.isConcrete[T]
    override def toString = "Label=" + name            
    def prettyPrint = name
  }

  abstract class Entity {
    type Level <: Syntax.this.Level
		def prettyPrint: String
  }
  
  abstract class Term extends Entity {
    type Level = Levels.Term
    
    def isPath = false
  }

  object Members {
    // the member's label (one level below L) and its classifier (at level L)
    case class Decl[+E <: Entity](l: Label[E#Level#Classifies], cls: E) {
			def prettyPrint = l.prettyPrint + ": " + cls.prettyPrint
		}
    // heterogeneous list of member declarations, each entry consists of
    type Decls = List[Decl[Entity]] // existential types aren't ready for prime time, I would say
    // -- try replacing Entity by E forSome {type E <: Entity} and see the whole project explode
  
    case class Def[+E <: Entity](l: Label[E#Level], rhs: E)
    type Defs[E <: Entity] = List[Def[E]]
  }

  object Terms {
    abstract class Value extends Term 

      case class Var(name: Name) extends Value {
        override def isPath = true
				override def prettyPrint = name.prettyPrint
      }
      case class Fun(tpe: Type, body: \\[Term]) extends Value {
				override def prettyPrint = "λ" + body.prettyPrint 
			}
  
    case class App(fun: Term, arg: Term) extends Term {
			 override def prettyPrint = fun.prettyPrint + "⋅" + arg.prettyPrint
		}
    case class New(tpe: Type, args_scope: \\[(Members.Defs[Terms.Value], Term)]) extends Term {
      // assert(tpe.isConcrete)
			override def prettyPrint = "new " + tpe.prettyPrint + args_scope.prettyPrint
    }
    case class Sel(tgt: Term, label: Label[Levels.Term]) extends Term {
      override def isPath = tgt.isPath
			override def prettyPrint = tgt.prettyPrint + "." + label.prettyPrint
    }

    case object Unit extends Value {
			override def prettyPrint = "()"
		}

//    object IdMap extends Map { def apply(tm: Term) = tm }
//    abstract class Map(tpMap: Types.Map = Types.IdMap,
//                       nameMap: Name => Name = identity,
//                       mdefMap: Members.Def => Members.Def = identity,
//                       labelMap: ((Label[E] => Label[E]) forSome {type E <: Entity}) = identity) extends (Term => Term) {
//      def mapOver(tm: Term) = tm match {
//        case Var(n) => Var(nameMap(n))
//        case Fun(tpe, body) => Fun(tpMap(tpe), body map this)
//        case App(fun, arg) => App(this(fun), this(arg))
//        case New(tpe, args_scope) => New(tpMap(tpe), args_scope map {case (mdefs, scope) => (mdefs map mdefMap, this(scope))})
//        case Sel(tgt, l) => Sel(this(tgt), labelMap(l))
//      }
//    }
  }
  
  abstract class Type extends Entity {
    type Level = Levels.Type
    def isConcrete = false
  }
  
  object Types {
    case class Sel(tgt: Term, label: Label[Levels.Type]) extends Type {
      assert(tgt.isPath)
      override def isConcrete = label.isConcrete
			override def prettyPrint = tgt.prettyPrint + "." + label.prettyPrint
    }
    
    case class Refine(parent: Type, decls: \\[Members.Decls]) extends Type {
      override def isConcrete = parent.isConcrete
			override def prettyPrint = parent.prettyPrint + " { " + decls.prettyPrint + " }"
    }
    
    case class Fun(from: Type, to: Type) extends Type {
			override def prettyPrint = from.prettyPrint + " → " + to.prettyPrint
		}
    
    case class Intersect(a: Type, b: Type) extends Type {
      override def isConcrete = a.isConcrete && b.isConcrete
			override def prettyPrint = a.prettyPrint + " ∧ " + b.prettyPrint
    }
    case class Union(a: Type, b: Type) extends Type {
			override def prettyPrint = a.prettyPrint + " ∨ " + b.prettyPrint
		}
    
    case object Top extends Type {
      override def isConcrete = true
			override def prettyPrint = "Top"
    }
    case object Bottom extends Type {
			override def prettyPrint = "⊥"
		}

//    object IdMap extends Map { def apply(tm: Term) = tm }
//    abstract class Map(tmMap: Terms.Map = Terms.IdMap,
//                       nameMap: Name => Name = identity,
//                       mdefMap: Members.DefMap = identity,
//                       mdeclMap: Members.DeclMap = IdMemDeclMap,
//                       labelMap: ((Label[E] => Label[E]) forSome {type E <: Entity}) = identity) extends (Term => Term) {
//      def mapOver(tp: Type) = tp match {
//        case Sel(tgt: Term, label: Label[Levels.Type]) =>
//        case Refine(parent: Type, decls: \\[Members.Decls]) => Refine(this(parent), decls map (_.map(mdeclMap)))
//        case Fun(from: Type, to: Type) => Fun(this(from), this(to))
//        case Intersect(a: Type, b: Type) => Intersect(this(a), this(b))
//        case Union(a: Type, b: Type) => Union(this(a), this(b))
//        case Top    => this(tp)
//        case Bottom => this(tp)
//      }
//    }
  }
  
  case class TypeBounds(lo: Type, hi: Type) extends Entity {
    type Level = Levels.TypeBounds
		override def prettyPrint = lo.prettyPrint + ".." + hi.prettyPrint
  }
}

trait NominalBindingSyntax extends Syntax with frescala.NominalBindingSyntax { self: Syntax =>
  implicit val termHasBinders: ContainsBinders[Term] = (tm: Term) => new Nominal[Term] {
    def swap(a: Name, b: Name): Term = { import Terms._// use Terms.Map
      tm match {
        case Var(n) => Var(n swap(a,b))
        case Fun(tpe, body) => Fun(tpe swap(a,b), body swap(a,b))
        case App(fun, arg) => App(fun swap(a,b), arg swap(a,b))
        case New(tpe, args_scope) => New(tpe swap(a,b), args_scope swap(a,b))
        case Sel(tgt, l) => Sel(tgt swap(a,b),  l swap(a,b))
      }
    }

    def fresh(a: Name): Boolean = { import Terms._// use Terms.Map
      tm match {
        case Var(n) => n fresh(a)
        case Fun(tpe, body) => tpe.fresh(a) && body.fresh(a)
        case App(fun, arg) => fun.fresh(a) && arg.fresh(a)
        case New(tpe, args_scope) => tpe.fresh(a) && args_scope.fresh(a)
        case Sel(tgt, l) => tgt.fresh(a) && l.fresh(a)
      }
    }
  }

  implicit val typeHasBinders: ContainsBinders[Type] = (tp: Type) => new Nominal[Type] {
    import Types._// use Types.Map

    def swap(a: Name, b: Name): Type = {
      tp match {
         case Sel(tgt, label) => Sel(tgt swap(a,b), label swap(a,b))
         case Refine(parent, decls) => Refine(parent swap(a,b), decls swap(a,b))
         case Fun(from, to) => Fun(from swap(a,b), to swap(a,b))
         case Intersect(tp1, tp2) => Intersect(tp2 swap(a,b), tp2 swap(a,b))
         case Union(tp1, tp2) => Union(tp2 swap(a,b), tp2 swap(a,b))
         case Top    => Top
         case Bottom => Bottom
      }
    }

    def fresh(a: Name): Boolean = {
      tp match {
         case Sel(tgt, label) =>  tgt.fresh(a) && label.fresh(a)
         case Refine(parent, decls) => parent.fresh(a) && decls.fresh(a)
         case Fun(from, to) => from.fresh(a) && to.fresh(a)
         case Intersect(tp1, tp2) => tp2.fresh(a) && tp2.fresh(a)
         case Union(tp1, tp2) => tp2.fresh(a) && tp2.fresh(a)
         case Top    => true
         case Bottom => true
      }
    }
  }

  implicit val typeBoundsHasBinders: ContainsBinders[TypeBounds] = (k: TypeBounds) => new Nominal[TypeBounds] {
    def swap(a: Name, b: Name): TypeBounds = {
      k match {
        case TypeBounds(lo, hi) => TypeBounds(lo swap(a,b), hi swap(a,b))
      }
    }

    def fresh(a: Name): Boolean = {
      k match {
        case TypeBounds(lo, hi) =>  lo.fresh(a) && hi.fresh(a)
      }
    }
  }

  implicit def labelHasBinders[T <: Level]: ContainsBinders[Label[T]] = AtomicIsNominal[Label[T]](_)

  implicit val valueHasBinders: ContainsBinders[Terms.Value] = (tm: Terms.Value) => new Nominal[Terms.Value] {
    import Terms._// use Terms.Map
    def swap(a: Name, b: Name): Value = {
      tm match {
        case Var(n) => Var(n swap(a,b))
        case Fun(tpe, body) => Fun(tpe swap(a,b), body swap(a,b))
      }
    }

    def fresh(a: Name): Boolean = {
      tm match {
        case Var(n) => n fresh(a)
        case Fun(tpe, body) => tpe.fresh(a) && body.fresh(a)
      }
    }
  }

//  object Members {
//    // the member's label (one level below L) and its classifier (at level L)
//    case class Decl[E <: Entity](l: Label[E#Level#Classifies], cls: E)
//    // heterogeneous list of member declarations, each entry consists of
//    type Decls = List[Decl[E forSome {type E <: Entity}]]
//
//    case class Def[E <: Entity](l: Label[E#Level], rhs: E)
//    type Defs[E <: Entity] = List[Def[E]]
//  }

  implicit def memDeclHasBinders[E <: Entity]: ContainsBinders[Members.Decl[E]] = (mem: Members.Decl[E]) => new Nominal[Members.Decl[E]] {
    import Members._// use Members.Map
    def swap(a: Name, b: Name): Decl[E] = {
      mem match {
        case d: Decl[TypeBounds] => Decl[TypeBounds](d.l swap(a,b), d.cls swap(a,b)).asInstanceOf[Decl[E]] //XXX
        case d: Decl[Type] => Decl[Type](d.l swap(a,b), d.cls swap(a,b)).asInstanceOf[Decl[E]] //XXX
      }
    }

    def fresh(a: Name): Boolean = {
      mem match {
        case d: Decl[TypeBounds] => d.l.fresh(a) && d.cls.fresh(a)
        case d: Decl[Type] => d.l.fresh(a) && d.cls.fresh(a)
      }
    }
  }

  implicit def memDefHasBinders[E <: Entity]: ContainsBinders[Members.Def[E]] = (mem: Members.Def[E]) => new Nominal[Members.Def[E]] {
    import Members._// use Members.Map
    def swap(a: Name, b: Name): Def[E] = {
      mem match {
        case d: Def[Term] => Def[Term](d.l swap(a,b), d.rhs swap(a,b)).asInstanceOf[Def[E]] //XXX
      }
    }

    def fresh(a: Name): Boolean = {
      mem match {
        case d: Def[Term] => d.l.fresh(a) && d.rhs.fresh(a)
      }
    }
  }
}