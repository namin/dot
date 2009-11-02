package scala.util.monads

// based in part on Graham Hutton and Erik Meijer. Monadic Parser Combinators.  (technical report NOTTCS-TR-96-4)

trait MonadCompanion[M[_]] {
  // returns the computation that yields the given value 
  implicit def result[A](x: A): M[A]
}

trait Monad[A, M[_]] {
  implicit val companion: MonadCompanion[M]  
  import companion._
  
  // chains this computation with the next one, `f`
  def >>=[B](f: A => M[B]): M[B] 
  
  
  def map[B](f: A => B): M[B]        = >>= {x => result(f(x))}
  def flatMap[B](f: A => M[B]): M[B] = >>=(f)
}

trait MonadZeroPlusCompanion[M[_]] extends MonadCompanion[M] {
  // returns the trivial computation
  implicit def zero[A]: M[A]
}

trait MonadZeroPlus[A, M[x] <: MonadZeroPlus[x, M]] extends Monad[A, M] {
  implicit override val companion: MonadZeroPlusCompanion[M]
  import companion._

  // the choice operator for computations, chose either this computation or `o`
  def ++(o: M[A]): M[A]
}
  
trait StateMonadCompanion[M[_], State] extends MonadCompanion[M] {
  def apply[A](fun: State => (A, State)): M[A]

  implicit def result[A](x: A): M[A] = apply((x, _))
  
  def update(f: State => State): M[State] = apply{s: State => (s, f(s))}
  def set(s: State): M[State] = update(x => s)
  def fetch = update(x => x)
}

trait StateMonad[A, M[x] <: StateMonad[x, M, State], State] extends Monad[A, M] {
  implicit override val companion: StateMonadCompanion[M, State]
  import companion._
  
  val initState: State
  val stateTrans: State => (A, State)

  def >>=[B](f: A => M[B]) = apply { currState => 
        val (a, nextState) = stateTrans(currState); f(a).stateTrans(nextState) }
        
  def run = stateTrans(initState)._1
}

//import scala.collection.mutable.HashMap
//
//object IntStateMonadCompanion extends StateMonadCompanion[IntStateMonad, HashMap[Int, Int]] {
//  def apply[A](fun: HashMap[Int, Int] => (A, HashMap[Int, Int])): IntStateMonad[A]  = new IntStateMonad(HashMap.empty, fun)
//}
//
//class IntStateMonad[A](override val initState: HashMap[Int, Int], override val stateTrans: HashMap[Int, Int] => (A, HashMap[Int, Int])) extends StateMonad[A, IntStateMonad, HashMap[Int, Int]] {
//  implicit override val companion = IntStateMonadCompanion
//}
//
//object Test {
//  import IntStateMonadCompanion._
//
//  type M[X] = IntStateMonad[X]
//
//  def fib(n: Int): M[Int] = n match {
//    case 0 => 0
//    case 1 => 1
//    case _ => for(r1 <- fib(n-1);
//                  r2 <- fib(n-2)) yield r1+r2
//  }
//}


trait ReaderMonadCompanion[M[_], State] extends MonadCompanion[M] {
  def apply[A](fun: State => A): M[A]

  implicit def result[A](x: A): M[A] = apply(currState => x)
}

trait ReaderMonad[A, M[x] <: ReaderMonad[x, M, State], State] extends Monad[A, M] {
  implicit override val companion: ReaderMonadCompanion[M, State]  
  import companion._

  val initState: State
  val stateTrans: State => A
  
  //def >>=[B](f: A => M[B]) = apply {currState => f(stateTrans(currState))}
        
  def run = stateTrans(initState)
}

/*
instance Monad0Plus m => Monad0Plus (StateM m s) where 
  -- zero :: StateM m s a 
  zero = \s -> zero 
  -- (++) :: StateM m s a -> StateM m s a -> StateM m s a 
  stm ++ stm� = \s -> stm s ++ stm� s
*/
  
// use this to make existing classes into Monads
trait MonadClass[M[_]] extends MonadCompanion[M] {
  implicit def witness[A](self: M[A]): Monad[A, M] = new Monad[A, M] {
    val companion = MonadClass.this
    def >>=[B](f: A => M[B]): M[B] = MonadClass.this.>>=(f)(self)
  }

  def >>=[A, B](f: A => M[B])(implicit self: M[A]): M[B]
  
  def map[A, B](f: A => B)(implicit self: M[A]): M[B]        = >>= {x: A => result(f(x))}
  def flatMap[A, B](f: A => M[B])(implicit self: M[A]): M[B] = >>=(f)
}
