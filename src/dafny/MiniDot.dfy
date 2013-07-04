//
// MiniDot
//

datatype option<A> = None | Some(get: A);

//
// Syntax
//
datatype tm = tvar(x: int)                                 // x                                            (variable)
            | tnew(mx: int, mf: tm, field: option<tm>, T: ty)// new { def apply(x)=t1; val get=t2; type T }  (object/function creation)
            | tapp(f: tm, a: tm)                           // t.apply(t)                                   (method call)
            | tget(o: tm)                                  // t.get                                        (field selection)
            ;

datatype ty = Top | Bot
            | TArrow(T1: ty, T2: ty)                       // { T1 => T2 }                                 (method)
            | TVal(Tv: ty)                                 // { val T }                                    (field member)
            | TTyp(T: ty)                                  // { type T }                                   (type member)
            | TSel(x: int)                                 // x.T                                          (type selection)
            ;

// G (type  env)
datatype context = Extend(k: int, v: ty, rest: context) | Empty;
function ty_lookup(k: int, L: context): result<ty>
  decreases L;
{
  match L
  case Empty => Stuck
  case Extend(k', v', L') => if (k'==k) then Result(v') else ty_lookup(k, L')
}

// H (value env)
datatype heap = Extend(k: int, v: vl, rest: heap) | Empty;
function vl_lookup(k: int, L: heap): result<vl>
  ensures vl_lookup(k, L).Result? ==> vl_lookup(k, L).get<L;
  decreases L;
{
  match L
  case Empty => Stuck
  case Extend(k', v', L') => if (k'==k) then Result(v') else vl_lookup(k, L')
}

datatype vl = Clos(H: heap, mx: int, mf: tm, field: option<vl>) // Clos H { def apply(x)=t; val get=v } (object/closure)

predicate sub(n: nat, G1: context, T1: ty, G2: context, T2: ty)
  decreases n, T1;
{
     (T2.Top?)
  || (T2.Bot?)
  || (n>0 && T1.TArrow? && T2.TArrow? && sub(n-1, G2, T2.T1, G1, T1.T1) && sub(n-1, G1, T1.T2, G2, T2.T2))
  || (T1.TVal? && T2.TVal? && sub(n, G1, T1.Tv, G2, T2.Tv))
  || (T1.TTyp? && T2.TTyp? && sub(n, G1, T1.T, G2, T2.T))
  || (n>0 && T1.TSel? && ty_lookup(T1.x, G1).Result? && sub(n-1, G1, ty_lookup(T1.x, G1).get, G2, T2))
  || (n>0 && T2.TSel? && ty_lookup(T2.x, G2).Result? && sub(n-1, G1, T1, G2, ty_lookup(T2.x, G2).get))
}

datatype result<A> = Result(get: A) | Stuck | TimeOut;

function chain(r1: result, r2: result): result
{
  match r1
  case Stuck => Stuck
  case TimeOut => TimeOut
  case Result(v) => r2
}

function eval(n: nat, H: heap, t: tm): result<vl>
  decreases n, t;
{
  match t
  case tvar(x) => vl_lookup(x, H)
  case tnew(mx, mf, t, T) =>
    if (t.Some?) then
      var v := eval(n, H, t.get);
      if !v.Result? then v else
      Result(Clos(H, mx, mf, Some(v.get)))
    else Result(Clos(H, mx, mf, None))
  case tapp(o, a) =>
    var vo := eval(n, H, o);
    var va := eval(n, H, a);
    if !vo.Result? || !va.Result? then chain(vo, va) else
    if n==0 then TimeOut else
    eval(n-1, heap.Extend(vo.get.mx, va.get, H), vo.get.mf)
  case tget(o) =>
    var vo := eval(n, H, o);
    if !vo.Result? then vo else
    if vo.get.field.None? then Stuck else
    Result(vo.get.field.get)
}

predicate typ(n: nat, G: context, t: tm, T: ty)
  decreases n, t;
{
     (t.tvar? && ty_lookup(t.x, G)==Result(T))
  || (t.tnew? && T.TArrow? && typ(n, context.Extend(t.mx, T.T1, G), t.mf, T.T2))
  || (t.tnew? && T.TVal? && t.field.Some? && typ(n, G, t.field.get, T.Tv))
  || (t.tnew? && T.TTyp? && t.T==T)
  || (t.tapp? && exists T1 :: typ(n, G, t.a, T1) && typ(n, G, t.f, TArrow(T1, T)))
  || (t.tget? && typ(n, G, t.o, TVal(T)))
  || (n>0 && exists T1 :: sub(n-1, G, T1, G, T) && typ(n-1, G, t, T1))
}

predicate wfenv(n: nat, H: heap, G: context)
  decreases H, n, 0;
{
  forall x :: vl_lookup(x, H).Result? ==> ty_lookup(x, G).Result? && vtyp_rec(n, G, vl_lookup(x, H).get, ty_lookup(x, G).get)
}

predicate vtyp(n: nat, v: vl, T: ty)
  decreases v, n, 2;
{
  exists G :: wfenv(n, v.H, G) && vtyp_rec(n, G, v, T)
}
predicate vtyp_rec(n: nat, G: context, v: vl, T: ty)
  decreases v, n, 1;
{
     (T.TArrow? && typ(n, context.Extend(v.mx, T.T1, G), v.mf, T.T2))
  || (T.TVal? && v.field.Some? && vtyp(n, v.field.get, T.Tv))
  || (n>0 && exists T1 :: sub(n-1, G, T1, G, T) && vtyp_rec(n-1, G, v, T1))
}