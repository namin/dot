package scala.dot

trait Syntax  { 
// <TODO inherited from frescala library>
  type \\[T]
  type Name
// </TODO>  
  
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
  
  trait IsConcrete[T <: Level] {val result: Boolean}
  implicit object concreteClassType extends IsConcrete[Levels.ClassType] { val result = true}
  def notConcrete[T <: Level] = new IsConcrete[T] { val result = false}
  def implicitlyDefault[T](default: T)(implicit v: T=default):T = v
  class Label[+T <: Level] {
    def isConcrete = implicitlyDefault[IsConcrete[T]](notConcrete).result
  }

  type MemDefs[E <: Entity] = List[(Label[E#Level], E)]
  // heterogeneous list of member declarations, each entry consists of
  // the member's label (one level below L) and its classifier (at level L)
  type MemDecls = List[(Label[E#Level#Classifies], E) forSome {type E <: Entity}]
  
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
    case class New(tpe: Type, args: \\[MemDefs[Value]]) extends Term
    case class Sel(tgt: Term, label: Label[Levels.Term]) extends Term {
      override def isPath = tgt.isPath
    }
  }
  
  class Type extends Entity {
    type Level = Levels.Type
    def isConcrete = false
  }
  
  object Types {
    case class Sel(tgt: Type, label: Label[Levels.Type]) extends Type {
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