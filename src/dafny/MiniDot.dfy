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
{
  sub_rec(n, G1, T1, G2, T2, true)
}

predicate sub_rec(n: nat, G1: context, T1: ty, G2: context, T2: ty, p: bool)
  decreases n, if (p) then T1 else T2;
{
     (T2.Top?)
  || (T1.Bot?)
  || (T1.TArrow? && T2.TArrow? && sub_rec(n, G2, T2.T1, G1, T1.T1, !p) && sub_rec(n, G1, T1.T2, G2, T2.T2, p))
  || (T1.TVal? && T2.TVal? && sub_rec(n, G1, T1.Tv, G2, T2.Tv, p))
  || (T1.TTyp? && T2.TTyp? && sub_rec(n, G1, T1.T, G2, T2.T, p))
  || (n>0 && T1.TSel? && ty_lookup(T1.x, G1).Result? && sub_rec(n-1, G1, ty_lookup(T1.x, G1).get, G2, T2, p))
  || (n>0 && T2.TSel? && ty_lookup(T2.x, G2).Result? && sub_rec(n-1, G1, T1, G2, ty_lookup(T2.x, G2).get, p))
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

predicate wf(n: nat, G: context, T: ty)
  decreases n, T;
{
     T.Top? || T.Bot?
  || (T.TArrow? && wf(n, G, T.T1) && wf(n, G, T.T2))
  || (T.TVal? && wf(n, G, T.Tv))
  || (T.TTyp? && wf(n, G, T.T))
  || (n>0 && T.TSel? && ty_lookup(T.x, G).Result? && wf(n-1, G, ty_lookup(T.x, G).get))
}

//
// Machinery
//
ghost method help_sub_rec_monotonic(n: nat, G1: context, T1: ty, G2: context, T2: ty, p: bool)
  requires sub_rec(n, G1, T1, G2, T2, p);
  ensures sub_rec(n+1, G1, T1, G2, T2, p);
  decreases n, if (p) then T1 else T2;
{
  if (n>0 && T1.TSel? && ty_lookup(T1.x, G1).Result? && sub_rec(n-1, G1, ty_lookup(T1.x, G1).get, G2, T2, p)) {
    help_sub_rec_monotonic(n-1, G1, ty_lookup(T1.x, G1).get, G2, T2, p);
  }
}
ghost method help_sub_rec_monotonic_plus(m: nat, n: nat, G1: context, T1: ty, G2: context, T2: ty, p: bool)
  requires sub_rec(m, G1, T1, G2, T2, p);
  requires m<=n;
  ensures sub_rec(n, G1, T1, G2, T2, p);
  decreases n-m;
{
  if (m<n) {
    help_sub_rec_monotonic(m, G1, T1, G2, T2, p);
    help_sub_rec_monotonic_plus(m+1, n, G1, T1, G2, T2, p);
  }
}

//
// Properties
//

ghost method lemma_sub_rec_refl(n: nat, G: context, T: ty, p: bool) returns (ns: nat)
  requires wf(n, G, T);
  ensures sub_rec(ns, G, T, G, T, p);
  decreases n, T;
{
  match T {
    case Top => ns := 0;
    case Bot => ns := 0;
    case TArrow(T1, T2) =>
      var ns1 := lemma_sub_rec_refl(n, G, T1, !p);
      var ns2 := lemma_sub_rec_refl(n, G, T2, p);
      ns := ns1+ns2;
      help_sub_rec_monotonic_plus(ns1, ns, G, T1, G, T1, !p);
      help_sub_rec_monotonic_plus(ns2, ns, G, T2, G, T2, p);
    case TVal(Tv) =>
      var nsv := lemma_sub_rec_refl(n, G, Tv, p);
      ns := nsv;
    case TTyp(Tt) =>
      var nst := lemma_sub_rec_refl(n, G, Tt, p);
      ns := nst;
    case TSel(x) =>
      var n1 := lemma_sub_rec_refl(n-1, G, ty_lookup(x, G).get, p);
      ns := n1+2;
  }
}

ghost method lemma_sub_rec_trans(n12: nat, n23: nat, G1: context, T1: ty, G2: context, T2: ty, G3: context, T3: ty, p: bool) returns (n13: nat)
  requires sub_rec(n12, G1, T1, G2, T2, p);
  requires sub_rec(n23, G2, T2, G3, T3, p);
  ensures sub_rec(n13, G1, T1, G3, T3, p);
  decreases if p then n12 else n23, if p then n23 else n12, if p then T1 else T3, T2, if p then T3 else T1;
{
  n13 := 0;
  if (T2.Top? && T3.TSel?) {
    var nr := lemma_sub_rec_trans(n12, n23-1, G1, T1, G2, T2, G3, ty_lookup(T3.x, G3).get, p);
    n13 := nr+1;
  }
  else if (T1.TArrow? && T2.TArrow? && T3.TArrow?) {
    var ns1 := lemma_sub_rec_trans(n23, n12, G3, T3.T1, G2, T2.T1, G1, T1.T1, !p);
    var ns2 := lemma_sub_rec_trans(n12, n23, G1, T1.T2, G2, T2.T2, G3, T3.T2, p);
    n13 := ns1+ns2;
    help_sub_rec_monotonic_plus(ns1, n13, G3, T3.T1, G1, T1.T1, !p);
    help_sub_rec_monotonic_plus(ns2, n13, G1, T1.T2, G3, T3.T2, p);
  }
  else if (T1.TVal? && T2.TVal? && T3.TVal?) {
    var nr := lemma_sub_rec_trans(n12, n23, G1, T1.Tv, G2, T2.Tv, G3, T3.Tv, p);
    n13 := nr;
  }
  else if (T1.TTyp? && T2.TTyp? && T3.TTyp?) {
    var nr := lemma_sub_rec_trans(n12, n23, G1, T1.T, G2, T2.T, G3, T3.T, p);
    n13 := nr;
  }
  else if (n12>0 && T1.TSel? && ty_lookup(T1.x, G1).Result? && sub_rec(n12-1, G1, ty_lookup(T1.x, G1).get, G2, T2, p)) {
    var nr := lemma_sub_rec_trans(n12-1, n23, G1, ty_lookup(T1.x, G1).get, G2, T2, G3, T3, p);
    n13 := nr+1;
  }
  else if (n12>0 && T2.TSel? && ty_lookup(T2.x, G2).Result? && sub_rec(n12-1, G1, T1, G2, ty_lookup(T2.x, G2).get, p)) {
    if (n23>0 && sub_rec(n23-1, G2, ty_lookup(T2.x, G2).get, G3, T3, p)) {
      var nr := lemma_sub_rec_trans(n12-1, n23-1, G1, T1, G2, ty_lookup(T2.x, G2).get, G3, T3, p);
      n13 := nr;
    }
    else if (n23>0 && T3.TSel? && ty_lookup(T3.x, G3).Result? && sub_rec(n23-1, G2, T2, G3, ty_lookup(T3.x, G3).get, p)) {
      var nr := lemma_sub_rec_trans(n12, n23-1, G1, T1, G2, T2, G3, ty_lookup(T3.x, G3).get, p);
      n13 := nr+1;
    }
  }
  else if (n23>0 && T2.TSel? && ty_lookup(T2.x, G2).Result? && sub_rec(n23-1, G2, ty_lookup(T2.x, G2).get, G3, T3, p)) {
    var nr := lemma_sub_rec_trans(n12, n23-1, G1, T1, G2, ty_lookup(T2.x, G2).get, G3, T3, p);
    n13 := nr+1;
  }
  else if (n23>0 && T3.TSel? && ty_lookup(T3.x, G3).Result? && sub_rec(n23-1, G2, T2, G3, ty_lookup(T3.x, G3).get, p)) {
    var nr := lemma_sub_rec_trans(n12, n23-1, G1, T1, G2, T2, G3, ty_lookup(T3.x, G3).get, p);
    n13 := nr+1;
  }
}
