package scala.dot
import scala.util.binding.frescala

trait Syntax extends BindingSyntax { 
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
  }

  type MemDefs[E <: Entity] = List[(Label[E#Level], E)]
  // heterogeneous list of member declarations, each entry consists of
  // the member's label (one level below L) and its classifier (at level L)
  type MemDecl = (Label[E#Level#Classifies], E) forSome {type E <: Entity}
  type MemDecls = List[MemDecl]
  
  class Entity {
    type Level <: Syntax.this.Level
  }
  
  class Term extends Entity {
    type Level = Levels.Term
    
    def isPath = false
  }
  
  object Terms {
    class Value extends Term
      case class Var(name: Name) extends Value {
        override def isPath = true
      }
      case class Fun(tpe: Type, body: \\[Term]) extends Value
  
    case class App(fun: Term, arg: Term) extends Term
    case class New(tpe: Type, args_scope: \\[(MemDefs[Value], Term)]) extends Term {
      assert(tpe.isConcrete)
    }
    case class Sel(tgt: Term, label: Label[Levels.Term]) extends Term {
      override def isPath = tgt.isPath
    }
  }
  
  class Type extends Entity {
    type Level = Levels.Type
    def isConcrete = false
  }
  
  object Types {
    case class Sel(tgt: Term, label: Label[Levels.Type]) extends Type {
      assert(tgt.isPath)
      override def isConcrete = label.isConcrete
    }
    case class Refine(parent: Type, decls: \\[MemDecls]) extends Type {
      override def isConcrete = parent.isConcrete
    }
    case class Fun(from: Type, to: Type) extends Type
    case class Intersect(a: Type, b: Type) extends Type {
      override def isConcrete = a.isConcrete && b.isConcrete
    }
    case class Union(a: Type, b: Type) extends Type
    case object Top extends Type {
      override def isConcrete = true
    }
    case object Bottom extends Type
  }
  
  case class TypeBounds(lo: Type, hi: Type) extends Entity {
    type Level = Levels.TypeBounds
  }
}

trait BindingSyntax extends frescala.BindingSyntax { self: Syntax =>  
  implicit val termHasBinders: ContainsBinders[Term]
  implicit def labelHasBinders[T <: Level]: ContainsBinders[Label[T]]
  implicit val valueHasBinders: ContainsBinders[Terms.Value]
  implicit val memDeclHasBinders: ContainsBinders[MemDecl]
}