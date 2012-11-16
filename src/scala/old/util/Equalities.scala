package scala.util

/**
 * Created by IntelliJ IDEA.
 * User: adriaan
 * Date: Nov 2, 2009
 * Time: 9:14:01 AM
 * To change this template use File | Settings | File Templates.
 */

trait Equalities {
  type ChecksEquality[T] = T => Equality[T]

  trait Equality[-T] {
	  def ===(a: T): Boolean
  }

  implicit def OptionEq[T : ChecksEquality](self: Option[T]) = new Equality[Option[T]] {
    def ===(other: Option[T]): Boolean = (for( s <- self; o <- other) yield s === o) getOrElse(true)
  }

  implicit def ListEq[T : ChecksEquality](self: List[T]) = new Equality[List[T]] {
    def ===(other: List[T]): Boolean = List.forall2(self, other)(_ === _) 
  }

}
