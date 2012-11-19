package dot

// based in part on:
// FreshLib and Scrap your Nameplate (Functional Pearl)
// by James Cheney, available at
// http://homepages.inf.ed.ac.uk/jcheney/programs/freshlib/

// NOTE(namin): digested nominal abstract syntax from:
// alphaKanren: A Fresh Name in Nominal Logic Programming
// by William E. Byrd and Daniel P. Friedman, available at
// http://www.cs.indiana.edu/~webyrd/

trait AbstractBindingSyntax {
  type ContainsBinders[T] 

  trait Scoped[T] { self: \\[T] =>
    def unabs: (Name, T)
    def map[U: ContainsBinders](f: T => U): \\[U] = {
      val (n, b) = unabs
      \\(n, f(b)) // TODO: make a version where f gets to see the new binder?
    }
  }

  type \\[T] <: Scoped[T] 
  val \\ : ScopedCompanion
  trait ScopedCompanion {
    def apply[T: ContainsBinders](binder: Name, body: T): \\[T]
    def unapply[T](scrutinee: \\[T]): Option[(Name, T)]
  }
  
  type Name 
  val Name : NameCompanion
  trait NameCompanion {
    def apply(s: String): Name
  }

//  implicit def listBinders[T: ContainsBinders]: ContainsBinders[List[T]]
//  implicit def pairBinders[T: ContainsBinders, U: ContainsBinders]: ContainsBinders[(T, U)]

  trait Substable[To, Res] {
    type From[T] = T => Substable[To, Res] // for use as context-bound
    def subst(from: Name, to: To): Res
  }

  // TODO: generalize similar to collect
  implicit def listIsSubstable[T: Substable[To, Res]#From, To, Res](in: List[T]): Substable[To, List[Res]] = new Substable[To, List[Res]] {
    def subst(from: Name, to: To): List[Res] = in map (_.subst(from, to))
  }

  implicit def pairIsSubstable[A: Substable[To, A2]#From, B: Substable[To, B2]#From, To, A2, B2](in: (A, B)): Substable[To, (A2, B2)] = new Substable[To, (A2, B2)] {
    def subst(from: Name, to: To): (A2, B2) = (in._1 subst(from, to), in._2 subst(from, to))
  }
}

trait NominalBindingSyntax extends AbstractBindingSyntax with Equalities {
  type ContainsBinders[T] = T => Nominal[T]

  trait Nominal[Self] {
    def swap(a: Name, b: Name): Self
    def fresh(a: Name): Boolean
  }

  def AtomicIsNominal[T](self: T): Nominal[T] = new Nominal[T] {
    def swap(a: Name, b: Name) = self
    def fresh(a: Name) = true
  }

  implicit val IntIsNominal = AtomicIsNominal[Int](_)
  implicit val StringIsNominal = AtomicIsNominal[String](_)
  implicit val UnitIsNominal = AtomicIsNominal[Unit](_)

  implicit def listBinders[T : ContainsBinders](self: List[T]) = new Nominal[List[T]] {
    def swap(a: Name, b: Name) = self map (_.swap(a, b))
    def fresh(a: Name) = self forall (_.fresh(a))
  }

  implicit def pairBinders[T : ContainsBinders, U: ContainsBinders](self: (T, U)) = new Nominal[(T, U)] {
    def swap(a: Name, b: Name) = (self._1.swap(a, b), self._2.swap(a, b)) // TODO: would be cool if we could do this generically for all Tuples (using HList-like approach)
    def fresh(a: Name) = self._1.fresh(a) && self._2.fresh(a)
  }

  object Name extends NameCompanion {
    private var nextId = 0
    def apply(s: String) = new Name(s)
  }

  // represents a binder, friendlyName is only used for toString
  class Name(friendlyName: String) extends Nominal[Name] with Equality[Name] {
    def \\[T : ContainsBinders](body: T): \\[T] = new \\(this, body)

    def genFresh: Name = Name(friendlyName)

    def swap(a: Name, b: Name) = if(this eq a) b else if(this eq b) a else this
    def fresh(a: Name) = this ne a

    final def ===(other: Name): Boolean = this eq other
    final override def equals(o: Any): Boolean = o match {
      case o : AnyRef => this eq o
      case _ => false
    }

    private val id: Int = {val r = Name.nextId; Name.nextId +=1; r }
    override def toString = friendlyName + "$" + id
  }

  object \\ extends ScopedCompanion {
    def apply[T: ContainsBinders](binder: Name, body: T) = new \\[T](binder, body)
    def unapply[T](scrutinee: \\[T]): Option[(Name, T)] = Some(scrutinee unabs)
  }

  class \\[T : ContainsBinders](private val binder: Name, private val body: T) extends Nominal[\\[T]] with Scoped[T] {
    def unabs: (Name, T) = {
      val newBinder = binder genFresh;
      
      (newBinder, body swap (binder, newBinder))
    }

    def swap(a: Name, b: Name) = \\(binder swap(a, b), body swap(a, b)) // boilerplate
    def fresh(a: Name) = if(a eq binder) true else body fresh (a)


// equality where caller may supply how to check equality of subterms
// needed in typer monad (when we want equality to force meta-variables instead of simply comparing them)
// to allow this, shouldn't implement Eq[\\[T]] directly
    def gequals[E[x] <: Equality[x]](other: \\[T])(implicit beq: T => E[T]): Boolean =
      (binder === other.binder) && (body === other.body) ||  // TODO: unchecked!
      (other.body.fresh(binder) && (body === other.body.swap(binder, other.binder)))

    def equals(other: \\[T]): Boolean =
      (binder == other.binder && body == other.body) ||  // TODO: unchecked!
      (other.body.fresh(binder) && body == other.body.swap(binder, other.binder))
    
    // meh
    override def equals(o: Any): Boolean = o match {
      case other: \\[_] => equals(other.asInstanceOf[\\[T]]) 
      case _ => false
    }

    override def toString() : String = binder + " \\\\ " + body
  }

  implicit def scopedEq[T](self: \\[T])(implicit beq: T => Equality[T]): Equality[\\[T]] = new Equality[\\[T]] {
    def ===(other: \\[T]): Boolean = self.gequals(other)(beq)
  }

  implicit def scopedIsSubstable[T: Substable[To, Res]#From, To, Res: ContainsBinders](in: \\[T]): Substable[To, \\[Res]] = new Substable[To, \\[Res]] {
    def subst(from: Name, to: To): \\[Res] = {
      val \\(z, b) = in
      \\(z, b subst(from, to))
    }
  }
}
