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
    // def defaultLabelBuilder[T <: Level] = new LabelBuilder[T]{def apply(n: String) = new Label(n)}
    // implicit object concreteClassTypeLabelBuilder extends LabelBuilder[Levels.ClassType] { 
    //   val labels = new scala.collection.mutable.HashMap[String, Label[Levels.ClassType]]
    //   def apply(n: String) = {
    //     assert(!labels.isDefinedAt(n))
    //     labels cached (n, new Label[Levels.ClassType](n))
    //   }
    // }

    // def apply[T <: Level](name: String)(implicit b: LabelBuilder[T] = defaultLabelBuilder[T]) = b(name)
  }
  
  abstract class Label[+T <: Level](val name: String) {
    def isConcrete = Label.isConcrete[T]
  }

	case class TypeLabel(override val name: String) extends Label[Levels.Type](name) {
			def apply(name: String) = new TypeLabel(name)
	}
	case class TermLabel(override val name: String) extends Label[Levels.Term](name) {
		 	def apply(name: String) = new TermLabel(name)		
	}

  abstract class Entity {
    type Level <: Syntax.this.Level
  }
  
  abstract class Term extends Entity {
    type Level = Levels.Term
    
    def isPath = false
  }

  object Members {
    // the member's label (one level below L) and its classifier (at level L)
    sealed abstract class Decl[+L <: Level, +E <: Entity](val l: Label[L], val cls: E) 
    // abstract case class Decl[+E <: Entity](l: Label[E#Level#Classifies], cls: E) 

		case class TypeBoundsDecl(override val l: TypeLabel, override val cls: TypeBounds) extends Decl[Levels.Type, TypeBounds](l, cls)
		case class TypeDecl(override val l: TermLabel, override val cls: Type) extends Decl[Levels.Term, Type](l, cls)

    // heterogeneous list of member declarations, each entry consists of
		type Decls = List[Decl[Level, Entity]] // existential types aren't ready for prime time, I would say
    // -- try replacing Entity by E forSome {type E <: Entity} and see the whole project explode
  
    abstract class Def[+E <: Entity](val l: Label[E#Level], val rhs: E)
		case class ValueDef(override val l: TermLabel, override val rhs: Terms.Value) extends Def[Term](l, rhs)

    type ValDefs = List[ValueDef]
  }

  object Terms {
    abstract class Value extends Term 

      case class Var(name: Name) extends Value {
        override def isPath = true
      }
      case class Fun(tpe: Type, body: \\[Term]) extends Value

    	case object Unit extends Value   

    case class App(fun: Term, arg: Term) extends Term 
    case class New(tpe: Type, args_scope: \\[(Members.ValDefs, Term)]) extends Term {
      // assert(tpe.isConcrete)
    }
    case class Sel(tgt: Term, label: TermLabel) extends Term {
      override def isPath = tgt.isPath
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
    case class Sel(tgt: Term, label: TypeLabel) extends Type {
      assert(tgt.isPath)
      override def isConcrete = label.isConcrete
    }
    
    case class Refine(parent: Type, decls: \\[Members.Decls]) extends Type {
      override def isConcrete = parent.isConcrete
    }
    
    case class Fun(from: Type, to: Type) extends Type 
    
    case class Intersect(a: Type, b: Type) extends Type {
      override def isConcrete = a.isConcrete && b.isConcrete
    }
    case class Union(a: Type, b: Type) extends Type {
		}
    
    case object Top extends Type {
      override def isConcrete = true
    }
    case object Bottom extends Type 

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
				case Terms.Unit => Terms.Unit
      }
    }

    def fresh(a: Name): Boolean = { import Terms._// use Terms.Map
      tm match {
        case Var(n) => n fresh(a)
        case Fun(tpe, body) => tpe.fresh(a) && body.fresh(a)
        case App(fun, arg) => fun.fresh(a) && arg.fresh(a)
        case New(tpe, args_scope) => tpe.fresh(a) && args_scope.fresh(a)
        case Sel(tgt, l) => tgt.fresh(a) && l.fresh(a)
				case Terms.Unit => true
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

	implicit def termLabelHasBinders: ContainsBinders[TermLabel] = AtomicIsNominal[TermLabel](_)
	implicit def typeLabelHasBinders: ContainsBinders[TypeLabel] = AtomicIsNominal[TypeLabel](_)

//  implicit def labelHasBinders[T <: Level, L <: Label[T]]: ContainsBinders[L] = AtomicIsNominal[L](_)

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



	// implicit def typeBoundsDeclHasBinders: ContainsBinders[Members.TypeBoundsDecl] = 
	// 	(decl: Members.TypeBoundsDecl) => new Nominal[Members.TypeBoundsDecl] {
	//     import Members._// use Members.Map
	//     def swap(a: Name, b: Name) = TypeBoundsDecl(decl.l.swap(a, b), decl.cls.swap(a, b))
	//     def fresh(a: Name): Boolean = decl.l.fresh(a) && decl.cls.fresh(a)
	// 	}
	// 
	// implicit def typeDeclHasBinders: ContainsBinders[Members.TypeDecl] = 
	// 	(decl: Members.TypeDecl) => new Nominal[Members.TypeDecl] {
	//     import Members._// use Members.Map
	//     def swap(a: Name, b: Name) = TypeDecl(decl.l.swap(a, b), decl.cls.swap(a, b))
	//     def fresh(a: Name): Boolean = decl.l.fresh(a) && decl.cls.fresh(a)
	// 	}


	// NOTE: are doing pattern matching here, because a refinement contains a set of type or type bounds declarations,
	// and each of those needs to be convertable to a Nominal
  implicit def memDeclHasBinders: ContainsBinders[Members.Decl[Level, Entity]] = (mem: Members.Decl[Level, Entity]) => new Nominal[Members.Decl[Level, Entity]] {
    import Members._// use Members.Map
    def swap(a: Name, b: Name): Members.Decl[Level, Entity] = {
      mem match {
        case TypeBoundsDecl(l, cls) => TypeBoundsDecl(l.swap(a,b), cls.swap(a,b))
        case TypeDecl(l, cls) => TypeDecl(l swap(a,b), cls swap(a,b))
      }
    }

    def fresh(a: Name): Boolean = {
      mem match {
        case TypeBoundsDecl(l, cls) => l.fresh(a) && cls.fresh(a)
        case TypeDecl(l, cls) => l.fresh(a) && cls.fresh(a)
      }
    }
	}

  // implicit def memDeclHasBinders[E <: Entity]: ContainsBinders[Members.Decl[E]] = (mem: Members.Decl[E]) => new Nominal[Members.Decl[E]] {
  //   import Members._// use Members.Map
  //   def swap(a: Name, b: Name): Decl[E] = {
  //     mem match {
  //       case d: Decl[TypeBounds] => TypeBoundsDecl(d.l swap(a,b), d.cls swap(a,b)).asInstanceOf[Decl[E]] //XXX
  //       case d: Decl[Type] => TypeDecl(d.l swap(a,b), d.cls swap(a,b)).asInstanceOf[Decl[E]] //XXX
  //     }
  //   }

  implicit def memDefHasBinders: ContainsBinders[Members.ValueDef] = (mem: Members.ValueDef) => new Nominal[Members.ValueDef] {
    import Members._// use Members.Map
    def swap(a: Name, b: Name): ValueDef = {
      mem match {
        case ValueDef(l, rhs) => ValueDef(l swap(a,b), valueHasBinders(rhs) swap(a,b))
      }
    }

    def fresh(a: Name): Boolean = {
      mem match {
        case ValueDef(l, rhs) => l.fresh(a) && valueHasBinders(rhs).fresh(a)
      }
    }
  }

  // implicit def memDefHasBindersT: ContainsBinders[Members.Def[]] = (mem: Members.Def[_]) => new Nominal[Members.Def[_]] {
  //   import Members._// use Members.Map
  //   def swap(a: Name, b: Name): Def[_] = {
  //     mem match {
  //       case ValueDef(l, rhs) => ValueDef(l swap(a,b), rhs swap(a,b))
  //     }
  //   }
  // 
  //   def fresh(a: Name): Boolean = {
  //     mem match {
  //       case ValueDef(l, rhs) => l.fresh(a) && rhs.fresh(a)
  //     }
  //   }
  // }
}