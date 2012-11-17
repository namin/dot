package dot

trait Equalities {
  type ChecksEquality[T] = T => Equality[T]

  trait Equality[-T] {
    def ===(a: T): Boolean
  }

  implicit def OptionEq[T : ChecksEquality](self: Option[T]) = new Equality[Option[T]] {
    def ===(other: Option[T]): Boolean = (for( s <- self; o <- other) yield s === o) getOrElse(true)
  }

  implicit def ListEq[T : ChecksEquality](self: List[T]) = new Equality[List[T]] {
    def ===(other: List[T]): Boolean = (self, other).zipped.forall(_ === _) 
  }
}
