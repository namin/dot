signature X = sig
  type T
  val v: T
  val f: T -> T
end
structure A = struct
  type T = int
  val v = 0
  val f = fn x => x + 1
end
structure B :> X = A
functor mkDoubler(arg: X) :> X where type T = arg.T = struct
  type T = arg.T
  val v = arg.v
  val f = arg.f o arg.f
end
structure A2 = mkDoubler(A);
val a: int = A2.f(A.v);
structure B2 = mkDoubler(B);
val b: B2.T = B2.f(B.v);
