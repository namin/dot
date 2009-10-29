package scala.dot
import scala.util.binding.frescala.AbstractBindingSyntax

import scala.util.monads._

trait TyperMonad extends AbstractBindingSyntax {
  // results of the monad
  sealed abstract class Result[A] extends Monad[A, Result] {
    object meta extends MonadCompanion[Result]{
      implicit def result[A](x: A) = Success(x)
    }
    def filter(pred: A => Boolean): Result[A]     
    def mapOutZero[M[_], B](f: A => M[B])(z: Result[B] => M[B]): M[B]
  } 
  
//  def Success[A](r: A): Success[A] = Success(r, List())
  
  // TODO: generalise res to deal with multiple results (Stream / List)
  case class Success[A](res: A) extends Result[A] {
    def >>=[B](next: A => Result[B]) = next(res) //concat (more map ((mo: () => Result[A]) => () => mo() >>= next))
    def filter(pred: A => Boolean): Result[A] = if(pred(res)) this else Failure("filtered out")
    def mapOutZero[M[_], B](f: A => M[B])(z: Result[B] => M[B]): M[B] = f(res)
  }
  
  case class Failure[A](msg: String) extends Result[A] {
    def >>=[B](next: A => Result[B]) = Failure[B](msg)
    def filter(pred: A => Boolean): Result[A] = this
    def mapOutZero[M[_], B](f: A => M[B])(z: Result[B] => M[B]): M[B] = z(Failure[B](msg))
  }
    
  object TyperMonad extends MonadCompanion {
    def apply[A](f: From => To[A]): TyperMonad[A] = new TyperMonad{def apply(from: From) = f(from)}
    
    // inject x into the monad
    def result[A](x: A) = TyperMonad{_ mapEnvTo(_y => Success(x))}
    def results[A](x: Iterable[A]): TyperMonad[A] = TyperMonad{ case From(st, env) => To(Stream.fromIterator(x.elements) map {x => (st, Success(x))})}
    def fail[A](msg: String) = TyperMonad{_ mapEnvTo(_y => Failure[A](msg))}

    def check(p: => Boolean) = result() filter(x => p)
  }

  
  // state that is carried along
  type State
    //def next = State(currTag+1)
  def initState: State

  type Env
  def initEnv: Env

  trait TyperMonad[A] extends (From => To[A]) with Monad[A, TyperMonad] {
    val meta = TyperMonad ; import meta._
  
    def filter(pred: A => Boolean): TyperMonad[A] = TyperMonad{x => this(x) filterRes(pred)}
      
    // chains this computation with the next one
    def >>=[B](next: A => TyperMonad[B]): TyperMonad[B] = TyperMonad{x => this(x) chainRes((st, r) => next(r)(x.state = st), To(_, _))}
	  
    def ++(alt: => TyperMonad[A]): TyperMonad[A] = TyperMonad{x => this(x) ++ alt(x) }
    
    def findAll = this(From(initState, initEnv)).tos map {case (st, r) => r} toList
    def run = this(From(initState, initEnv)).tos map {case (st, r) => r} find{case Success(_) => true; case _ => false}
  } 

    
  case class From(st: State, env: Env) { // current state and environment
    def state = st
    def state_= (newSt: State) = From(newSt, env) // why can't I name this st_= ?
    def mapEnv(f: Env => Env) = From(st, f(env))
    def mapEnvTo[A](f: Env => Result[A]) = To(st, f(env))
    def mapStateTo[A](next: State => State, f: State => Result[A]) = {val n = next(st); To(n, f(n))}
  }
  
  def To[A](st: State, r: Result[A]): To[A] = To(Stream.fromIterator(List((st, r)).elements))
  case class To[A](tos: Stream[(State, Result[A])]) { // next state and result
    def filterRes(pred: A => Boolean) = mapRes(_.filter(pred))

    // if non-zero, compute the next state every element
    // zero: return zero (default element, can't be computed using the previous function)      
    def chainRes[B](f: (State, A) => To[B], z: (State, Result[B]) => To[B]): To[B] =
      mapStRes{case (st, r) => r.mapOutZero[To, B](x => f(st, x))(x => z(st, x))} 

    def mapRes[B](f: Result[A] => Result[B]): To[B] = To(tos map {case (st, r) => (st, f(r))})
    def mapStRes[B](f: (State, Result[A]) => To[B]): To[B] = To(tos.flatMap {case (st, r) => f(st, r).tos})
    def ++(alt: => To[A]): To[A] = To(tos append alt.tos)
  }
  
  def sequence[T](s: Option[TyperMonad[T]]): TyperMonad[Option[T]] = error("TODO") 
  def sequence[T](s: Set[TyperMonad[T]]): TyperMonad[Set[T]] = error("TODO")

}


/*

  trait Equality[T] {
	  def ===(a: T): Boolean
  }

  // deep equality that also does unification of MetaVar's 
  trait CheckingEquality[A] extends Equality[A] {
    def ===(other: A): Boolean
  }
  
  implicit def OptionCEq[T : CheckingEquality](self: Option[T]): CheckingEquality[Option[T]] = new CheckingEquality[Option[T]] {
    def ===(other: Option[T]): Boolean = (for( s <- self; o <- other) yield s === o) getOrElse(true)
  }

  implicit def NameCEq(self: Name): CheckingEquality[Name] = new CheckingEquality[Name] {
    def ===(other: Name): Boolean = self == other
  }
  
  implicit def AbsCEq[T : CheckingEquality](x: \\[T]): CheckingEquality[\\[T]] = new CheckingEquality[\\[T]] {
    def ===(a: \\[T]): Boolean = x.gequals[CheckingEquality](a)
  }

  // facilities for bidirectional type checking (logic programming, really)
  abstract class Expected[A : CheckingEquality] {
    def :=(tp: A): TyperMonad[Unit]
    def unary_! : TyperMonad[A]
  }

  def Infer[A : CheckingEquality](n: String): Infer[A] = new Infer[A](n: String)
  class Infer[A : CheckingEquality](val name: String) extends Expected[A] {
    private var tp: Option[A] = None 
    def :=(tp: A): TyperMonad[Unit] = TyperMonad.result(this.tp=Some(tp))
    def unary_! = tp map {TyperMonad.result(_)} getOrElse TyperMonad.fail("inference of "+name+" failed")
  }
  
  case class Check[A : CheckingEquality](val tp: A) extends Expected[A] {
    def :=(tp: A): TyperMonad[Unit] = 
      if(this.tp === tp) {
        println("check: "+this.tp+" == "+tp)
        TyperMonad.result(()) 
      } else {
        println("check: "+this.tp+" != "+tp)
        TyperMonad.fail("type checking failed") 
      }
    def unary_! = TyperMonad.result(tp)
  }
  
  // meta variable used by the type checker
  trait MetaVar[T] extends CheckingEquality[T] { self: T with MetaVar[T] =>
    val name: String
    var v: Option[T]
    
    def swap(a: Name, b: Name) = this
    def fresh(a: Name) = true
    def supp = List()
    
    // if this variable unifies with o, return Some(o)  -- TODO: use dependent method type Option[o.type]
    def unifies(o: T): Option[T]
    
    def unify(o: T): Boolean = {
      assert(v.isEmpty)
      println("unified "+this+" to "+o)
      v = unifies(o)
      !v.isEmpty
    }
    
    def unary_! = v map {TyperMonad.result(_)} getOrElse TyperMonad.fail("meta variable "+name+" not set")
    
    // if set, check against that -- if not set, unify with o and return true
    override def ===(o: T) = // v map{_ === o} getOrElse(unify(o))
      v match { 
        case Some(v) => !unifies(v).isEmpty
        case None => unify(o) 
      }  
    
  }  
*/