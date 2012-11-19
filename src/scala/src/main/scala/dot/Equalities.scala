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

  implicit def PairEq[A : ChecksEquality, B: ChecksEquality](self: (A,B)) = new Equality[(A,B)] {
    def ===(other: (A,B)): Boolean = self._1===other._1 && self._2===other._2
  }
}
