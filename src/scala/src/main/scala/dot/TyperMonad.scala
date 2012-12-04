package dot

// based in part on:
// Practical type inference for arbitrary-rank types
// by Simon Peyton Jones et al
// http://research.microsoft.com/en-us/um/people/simonpj/papers/higher-rank/index.htm

import collection.immutable.HashMap
import collection.Traversable

trait TyperMonad extends AbstractBindingSyntax with Debug {
  // results of the monad
  sealed abstract class Result[A] extends Monad[A, Result] {
    object companion extends MonadCompanion[Result]{
      implicit def result[A](x: A) = TyperSuccess(x)
    }
    def filter(pred: A => Boolean): Result[A]     
    def mapOutZero[M[_], B](f: A => M[B])(z: Result[B] => M[B]): M[B]
  } 
  
//  def Success[A](r: A): Success[A] = Success(r, List())
  
  // TODO: generalise res to deal with multiple results (Stream / List)
  case class TyperSuccess[A](res: A) extends Result[A] {
    def >>=[B](next: A => Result[B]) = next(res) //concat (more map ((mo: () => Result[A]) => () => mo() >>= next))
    def filter(pred: A => Boolean): Result[A] = if(pred(res)) TyperSuccess.this else TyperFailure("filtered out")
    def mapOutZero[M[_], B](f: A => M[B])(z: Result[B] => M[B]): M[B] = f(res)
  }
  
  case class TyperFailure[A](msg: String) extends Result[A] {
    def >>=[B](next: A => Result[B]) = TyperFailure[B](msg)
    def filter(pred: A => Boolean): Result[A] = TyperFailure.this
    def mapOutZero[M[_], B](f: A => M[B])(z: Result[B] => M[B]): M[B] = z(TyperFailure[B](msg))
  }
    
  object TyperMonad extends MonadCompanion[TyperMonad] {
    def apply[A](f: From => To[A]) = new TyperMonad[A]{def apply(from: From) = f(from)}
    
    // inject x into the monad
    implicit def result[A](x: A) = TyperMonad{_ mapEnvTo(_y => TyperSuccess(x))}
    def results[A](x: Iterable[A]): TyperMonad[A] = TyperMonad{ case From(st, env) => To(x.toStream map {x => (st, TyperSuccess(x))})}
    def fail[A](msg: String) = TyperMonad{_ mapEnvTo(_y => TyperFailure[A](msg))}

    def check(p: => Boolean) = result() filter(x => p)

    // chain the computations yielded by f(x) for all x in xs, so that, if f(x) is a failure for some x in xs,
    // the computation produced by forall fails; the computation succeeds iff, for all x in xs, f(x) succeeds
    def forall[T](xs: Traversable[T])(f: T => TyperMonad[Unit]): TyperMonad[Unit] =
      (xs map f).foldLeft(result(())){(acc, fx) => acc >>= {_ => fx}}


    def exactlyOne[T](xs: Traversable[T], err: String="required exactly 1 element"): TyperMonad[T] =
      if(xs.size == 1) result(xs.head)
      else fail(err)


    // returns some computation that succeeds or else fails with the given error
    def some[A](ms: List[TyperMonad[A]], err: String=null): TyperMonad[A] = ms match {
      case Nil => assert(err!=null); fail(err)
      case m::Nil if err==null => m
      case m::ms =>  TyperMonad{x =>
        val mx = m(x)
        mx mapStRes {
          case (_, r:TyperSuccess[A]) => mx
          case (_, r:TyperFailure[A]) => some(ms, err)(x)
        }
      }
    }
  }
  
  // state that is carried along
  type State
    //def next = State(currTag+1)
  def initState: State

  type Env
  def initEnv: Env

  trait TyperMonad[A] extends (From => To[A]) with Monad[A, TyperMonad] {
    val companion = TyperMonad ; import companion._

    def filter(pred: A => Boolean): TyperMonad[A] = TyperMonad{x => this(x) filterRes(pred)}
    def withFilter(pred: A => Boolean) = new WithFilter[A](this, pred)
    final class WithFilter[+A](self: TyperMonad[A], pred: A => Boolean) {
      def map[B](f: A => B): TyperMonad[B] = self filter pred map f
      def flatMap[B](f: A => TyperMonad[B]): TyperMonad[B] = self filter pred flatMap f
      def withFilter(q: A => Boolean): WithFilter[A] = new WithFilter[A](self, x => pred(x) && q(x))
    }

    // chains this computation with the next one
    def >>=[B](next: A => TyperMonad[B]): TyperMonad[B] = TyperMonad{x => this(x) chainRes((st, r) => next(r)(x.state = st), To(_, _))}

    def ++(alt: => TyperMonad[A]): TyperMonad[A] = TyperMonad{x => this(x) ++ alt(x) }
    
    def findAll(env: Option[Env] = None) = this(From(initState, env.getOrElse(initEnv))).tos map {case (st, r) => r} toList
    def findExactlyOne(env: Option[Env] = None) = {
      val r = findAll(env)
      assert(r.length==1, "result is not unique")
      r.head
    }
    def run = this(From(initState, initEnv)).tos map {case (st, r) => r} find{case TyperSuccess(_) => true; case _ => false}
  } 

    
  case class From(st: State, env: Env) { // current state and environment
    def state = st
    def state_= (newSt: State) = From(newSt, env) // why can't I name this st_= ?
    def mapEnv(f: Env => Env) = From(st, f(env))
    def mapEnvTo[A](f: Env => Result[A]) = To(st, f(env))
    def mapStateTo[A](next: State => State, f: State => Result[A]) = {val n = next(st); To(n, f(n))}
  }
  
  def To[A](st: State, r: Result[A]): To[A] = To(Stream((st, r)))
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
  
  def sequence[T](s: Option[TyperMonad[T]]): TyperMonad[Option[T]] = sys.error("TODO") 
  def sequence[T](s: Set[TyperMonad[T]]): TyperMonad[Set[T]] = sys.error("TODO")

}

trait MetaVariables extends AbstractBindingSyntax with TyperMonad with Equalities {
  // facilities for bidirectional type checking (logic programming, really)
  abstract class Expected[A : ChecksEquality] {
    protected var res: Option[A] = None

    def :=(tp: A): TyperMonad[Unit]
    def unary_! : TyperMonad[A]

    def toMetaVar[To: MetaVarOf[A]#To]: To = MetaVar(res)

    def unknown: Boolean = res.isEmpty
  }

  object Infer {
    def apply[A : ChecksEquality](n: String): Infer[A] = new Infer[A](n)
  }
  class Infer[A : ChecksEquality](val name: String) extends Expected[A] {
    def :=(o: A): TyperMonad[Unit] = {
      debug("infer " + this + " is " + o)
      TyperMonad.result(res=Some(o))
    }
    def unary_! = res map {TyperMonad.result(_)} getOrElse TyperMonad.fail("could not infer "+name)
    override def toString = name + "$infer(" + res + ")"
  }

  object Check {
    def apply[A : ChecksEquality](proto: A): Check[A] = new Check[A](proto)
  }
  class Check[A : ChecksEquality](val proto: A) extends Expected[A] {
    res = Some(proto)

    def :=(o: A): TyperMonad[Unit] =
      if(proto === o) {
        debug("check: "+ proto +" == "+ o)
        TyperMonad.result(())
      } else {
        debug("check: "+ proto +" != "+ o)
        TyperMonad.fail("type checking failed")
      }

    def unary_! = TyperMonad.result(proto)

    override def toString = "$check(" + proto + ")"
  }

  abstract class MetaVarBuilder[-From, +To](protoName: String) extends (Option[From] => To) {
    protected[this] def apply(n: String): (To with MetaVar[From])

    private[this] def make: (To with MetaVar[From]) = apply(freshName(protoName))

    private var id = 0
    private def genId = {id = id + 1; id-1}
    def freshName(n: String) = n+"$"+genId
    def apply(proto: Option[From]): To = {
      val res = make
      res.v = proto
      res
    }
  }
  trait MetaVarOf[A] { type To[to] = MetaVarBuilder[A, to]}
  object MetaVar {
    def apply[A, To: MetaVarOf[A]#To](x: Option[A]): To = implicitly[MetaVarBuilder[A, To]].apply(x)
  }
  // meta variable used by the type checker
  trait MetaVar[T] extends Equality[T] { //self: T with MetaVar[T] =>
    val name: String
    private[MetaVariables] var v: Option[T] = None

    // if this variable unifies with o, return Some(o)  -- TODO: use dependent method type Option[o.type]
    // TODO: switch to filter/withFilter-based scheme
    def unifies(o: T): Option[T] = Some(o)

    def unify(o: T): Boolean = {
      assert(v.isEmpty) // or unify silently when o == v.get ?
      debug("unified "+this+" to "+o)
      v = unifies(o)
      !v.isEmpty
    }

    def unary_! = v map {TyperMonad.result(_)} getOrElse TyperMonad.fail("meta variable "+name+" not set")

    // if set, check against that -- if not set, unify with o and return true
    final override def ===(o: T) = // v map{_ === o} getOrElse(unify(o))
      v match {
        case Some(v) => unifies(v).isDefined
        case None => unify(o)
      }

    override def toString = name + "$mv(" + v + ")"
  }
}

trait MetaVariablesNominal extends MetaVariables with NominalBindingSyntax {
  implicit def MetaVarNominal[T](mv: MetaVar[T]): Nominal[MetaVar[T]] = new Nominal[MetaVar[T]] {
    def swap(a: Name, b: Name) = mv // okay because fresh always returns false
    def fresh(a: Name) = false // we can't alpha-rename the meta-variable to ensure `a` is not bound
  }

  object MetaScoped {
    def apply[MT <: MetaVar[T] with T, T : ContainsBinders](name: String, body: MT) = new MetaScoped[MT, T](name, body)
  }
  class MetaScoped[MT <: MetaVar[T] with T, T : ContainsBinders](val name: String, body: MT) extends {val binder: Name = new Name(name)} with \\[T](binder, body) with MetaVar[\\[T]] {
    // do not generate fresh names when going under binder (unifies relies on this)
    override def unabs: (Name, T) = (binder, body)

    override def unifies(o: \\[T]): Option[\\[T]] = {
      val \\(zo, bo) = o

      // freshness check is needed: binder should be fresh everywhere, so if it isn't in bo (it's a metavar), swapping does not make sense
      if(bo fresh(binder)) body.unifies(bo swap(zo, binder)) map {b: T => \\(binder, b)}
      else None
    }
  }

}
trait StandardTyperMonad extends TyperMonad with MetaVariables {
  type Type
  
  // gamma, maps Name to Type
  type Env = Map[Name, Type]
  lazy val initEnv: Env = HashMap()

  def under[A, T](scoped: \\[T], tp: Type)(in: (Name, T) => TyperMonad[A]): TyperMonad[A]
    = for(\\(x, b) <- TyperMonad.result(scoped); res <- assume(x, tp)(in(x,b))) yield res

  def force[A, T](meta: MetaVar[T] with T)(in: T => TyperMonad[A]): TyperMonad[T]
    = for(_ <- in(meta); res <- !meta) yield res

  def force[A, T](meta: Expected[T])(in: Expected[T] => TyperMonad[A]): TyperMonad[T]
    = for(_ <- in(meta); res <- !meta) yield res

  def assume[A](vr: Name, tp: Type)(in: TyperMonad[A]): TyperMonad[A] = TyperMonad{x =>
    in(x mapEnv {_ + (vr -> tp)})
  }

  def getGamma: TyperMonad[Env] = TyperMonad{_ mapEnvTo(x => TyperSuccess(x)) }

  def lookup(n: Name): TyperMonad[Type] = getGamma >>= {
    _.get(n) match {
    case Some(t) => debug("looked up "+t); TyperMonad.result(t)
    case None => TyperMonad.fail("unbound " + n)
    }
  }
}
