signature X = sig
  type T
  val v: T
  val f: T -> T
end
structure XIntTransparent = struct
  type T = int
  val v = 0
  val f = fn x => x + 1
end
structure XIntOpaque :> X = XIntTransparent
functor mkDoubler(arg: X) :> X where type T = arg.T = struct
  type T = arg.T
  val v = arg.v
  val f = arg.f o arg.f
end
structure XIntTransparent' = mkDoubler(XIntTransparent);
val a: int = XIntTransparent'.f(XIntTransparent.v);
structure XIntOpaque' = mkDoubler(XIntOpaque);
val b: XIntOpaque'.T = XIntOpaque'.f(XIntOpaque.v);
