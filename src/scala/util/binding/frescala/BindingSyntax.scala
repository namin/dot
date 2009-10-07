package scala.util.binding.frescala


trait Binding { self: BindingSyntax with Binding => 
  trait Nominal[Self] {
    def swap(a: Name, b: Name): Self
    def fresh(a: Name): Boolean
  }

  implicit def IntIsNominal(self: Int): Nominal[Int] = new Nominal[Int] {
    def swap(a: Name, b: Name) = self
    def fresh(a: Name) = true
  }  

  implicit def CharIsNominal(self: Char): Nominal[Char] = new Nominal[Char] {
    def swap(a: Name, b: Name) = self
    def fresh(a: Name) = true
  } 
  
  implicit def UnitIsNominal(self: Unit): Nominal[Unit] = new Nominal[Unit] {
    def swap(a: Name, b: Name) = self
    def fresh(a: Name) = true
  }   
  
// can't abstract over Iterable here because it isn't defined like that in std lib
  
  implicit def ListIsNominal[T <% Nominal[T]](self: List[T]): Nominal[List[T]] = new Nominal[List[T]] {
    def swap(a: Name, b: Name) = self map (_.swap(a, b))    
    def fresh(a: Name) = self forall (_.fresh(a))
  }   
  
  implicit def OptionIsNominal[T <% Nominal[T]](self: Option[T]): Nominal[Option[T]] = new Nominal[Option[T]] {
    def swap(a: Name, b: Name) = self map (_.swap(a, b))    
    def fresh(a: Name) = self forall (_.fresh(a))
  }     
  
  implicit def SetIsNominal[T <% Nominal[T]](self: Set[T]): Nominal[Set[T]] = new Nominal[Set[T]] {
    def swap(a: Name, b: Name) = self map (_.swap(a, b))    
    def fresh(a: Name) = self forall (_.fresh(a))
  }     
  
}

trait BindingSyntaxCore {
  type ContainsBinders[T]
  
  type \\[T]
  def \\[T: ContainsBinders](n: Name, body: T): \\[T]
  
  type Name
  def Name(n: String): Name
  
  implicit def listBinders[T: ContainsBinders]: ContainsBinders[List[T]] = error("")
  implicit def pairBinders[T: ContainsBinders, U: ContainsBinders]: ContainsBinders[(T, U)] = error("")
}


trait BindingSyntax { self: AbsM with Binding with Substitution with BindingSyntax =>
  trait Equality[T] {
  	def ===(a: T): Boolean
  }

  case class Name(tag: Tag, s: String) extends Nominal[Name] {
    def \\[T](body: T)(implicit c: T => Nominal[T]): \\[T] = new \\[T](this, body)
    
    override def equals(o: Any): Boolean = o match {
      case Name(t, _) if tag == t => true
      case _ => false
    }
    
    def swap(a: Name, b: Name) = if(this == a) b else if(this == b) a else this
    def fresh(a: Name) = this != a
    
    override def toString = s + "$" + tag
  }

  def gensym(s: String): AM[Name] = for( t <- AM.newTag) yield Name(t, s)
  def rename(a: Name): AM[Name] = for( t <- AM.newTag) yield Name(t, a.s)

  object \\ {
    def apply[T](binder: Name, body: T)(implicit c: T => Nominal[T]) = new \\[T](binder, body)
    def unapply[T](scrutinee: \\[T])(implicit c: T => Nominal[T]): Option[AM[(Name, T)]] = Some(scrutinee unabs)
  }

  class \\[T](private[BindingSyntax] val binder: Name, private[BindingSyntax] val body: T)(
              implicit val cn: T => Nominal[T]) extends Nominal[\\[T]] {
        
    def unabs: AM[(Name, T)] = for(newBinder <- rename(binder)) 
        yield (newBinder, body swap (binder, newBinder))
        
    override def equals(o: Any): Boolean = o match {
      case other: \\[T] => (binder == other.binder && body == other.body) ||  // TODO: unchecked!
          (other.body.fresh(binder) && body == other.body.swap(binder, other.binder))
      case _ => false
    }

    
    def gequals[Eq[x] <: Equality[x] ](other: \\[T])(implicit neq: Name => Eq[Name], beq: T => Eq[T]): Boolean = (binder === other.binder) && (body === other.body) ||  // TODO: unchecked!
          (other.body.fresh(binder) && (body === other.body.swap(binder, other.binder)))
    
    def swap(a: Name, b: Name) = \\(binder swap(a, b), body swap(a, b)) // boilerplate
    def fresh(a: Name) = if(a == binder) true else body fresh (a)
  }


}

