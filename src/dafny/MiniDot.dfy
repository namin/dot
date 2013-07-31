//
// MiniDot
//

datatype option<A> = None | Some(get: A);
datatype result<A> = Result(get: A) | Stuck | TimeOut;

function chain(r1: result, r2: result): result
{
  match r1
  case Stuck => Stuck
  case TimeOut => TimeOut
  case Result(v) => r2
}

//
// Syntax
//
datatype tm = tnum(n: int)                                 // n                                            (constant number) 
            | tvar(x: int)                                 // x                                            (variable)
            | tnew(mx: int, mf: tm, field: tm, T: ty)      // new { def apply(x)=t1; val get=t2; type T }  (object/function creation)
            | tapp(f: tm, a: tm)                           // t.apply(t)                                   (method call)
            | tget(o: tm)                                  // t.get                                        (field selection)
            ;

datatype ty = Top | Bot | TInt
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

datatype vl = Num(n: int)                               // n                                    (constant number)
            | Clos(H: heap, mx: int, mf: tm, field: vl) // Clos H { def apply(x)=t; val get=v } (object/closure)

// Dynamic Semantics            
function eval(n: nat, H: heap, t: tm): result<vl>
  decreases n, t;
{
  match t
  case tnum(n) => Result(Num(n))
  case tvar(x) => vl_lookup(x, H)
  case tnew(mx, mf, t, T) =>
    var v := eval(n, H, t);
    if !v.Result? then v else
    Result(Clos(H, mx, mf, v.get))
  case tapp(o, a) =>
    var vo := eval(n, H, o);
    var va := eval(n, H, a);
    if !vo.Result? || !va.Result? then chain(vo, va) else
    if n==0 then TimeOut else
    if !vo.get.Clos? then Stuck else
    eval(n-1, heap.Extend(vo.get.mx, va.get, vo.get.H), vo.get.mf)
  case tget(o) =>
    var vo := eval(n, H, o);
    if !vo.Result? then vo else
    if !vo.get.Clos? then Stuck else
    Result(vo.get.field)
}

// Static Semantics
predicate path_eval(n: nat, G: context, x: int, T: ty)
{
  n>0 && ty_lookup(x, G).Result? && ty_lookup(x, G).get==T && wf(n-1, G, T)
}

predicate wf(n: nat, G: context, T: ty)
{
     (T.Top?)
  || (T.Bot?)
  || (T.TInt?)
  || (T.TArrow? && wf(n, G, T.T1) && wf(n, G, T.T2))
  || (T.TVal? && wf(n, G, T.Tv))
  || (T.TTyp? && wf(n, G, T.T))
  || (n>0 && T.TSel? && exists Tx :: path_eval(n-1, G, T.x, Tx))
}

predicate sub(n: nat, G1: context, T1: ty, G2: context, T2: ty)
{
  sub_rec(n, G1, T1, G2, T2, true)
}

predicate sub_rec(n: nat, G1: context, T1: ty, G2: context, T2: ty, p: bool)
  decreases n, if (p) then T1 else T2;
{
     (T2.Top?)
  || (T1.Bot?)
  || (T1.TInt? && T2.TInt?)
  || (T1.TArrow? && T2.TArrow? && sub_rec(n, G2, T2.T1, G1, T1.T1, !p) && sub_rec(n, G1, T1.T2, G2, T2.T2, p))
  || (T1.TVal? && T2.TVal? && sub_rec(n, G1, T1.Tv, G2, T2.Tv, p))
  || (T1.TTyp? && T2.TTyp? && sub_rec(n, G1, T1.T, G2, T2.T, p))
  || (n>0 && T1.TSel? && exists T1x :: path_eval(n, G1, T1.x, T1x) && sub_rec(n-1, G1, T1x, G2, T2, p))
  || (n>0 && T2.TSel? && exists T2x :: path_eval(n, G2, T2.x, T2x) && sub_rec(n-1, G1, T1, G2, T2x, p))
}

predicate typ(n: nat, G: context, t: tm, T: ty)
  decreases n, t;
{
     (t.tnum? && T.TInt?)
  || (t.tvar? && ty_lookup(t.x, G)==Result(T) && wf(n, G, T))
  || (t.tnew? &&
      exists TA1, TA2, Tv ::
      typ(n, context.Extend(t.mx, TA1, G), t.mf, TA2) && typ(n, G, t.field, Tv) &&
      wf(n, G, t.T) &&
      wf(n, G, TArrow(TA1, TA2)) &&
      ((T.TArrow? && T.T1==TA1 && T.T2==TA2) ||
       (T.TVal? && T.Tv==Tv) ||
       (T.TTyp? && T.T==t.T)))
  || (t.tapp? && exists T1 :: typ(n, G, t.a, T1) && typ(n, G, t.f, TArrow(T1, T)))
  || (t.tget? && typ(n, G, t.o, TVal(T)))
  || (n>0 && exists T1 :: sub(n-1, G, T1, G, T) && typ(n-1, G, t, T1))
}

predicate wfenv(n: nat, H: heap, G: context)
  decreases n, H, 0;
{
  forall x :: vl_lookup(x, H).Result? ==> ty_lookup(x, G).Result? && vtyp(n, G, vl_lookup(x, H).get, ty_lookup(x, G).get)
}

predicate vtyp(n: nat, G: context, v: vl, T: ty)
  decreases n, v;
{
     (T.TInt? && v.Num?)
  || (T.TArrow? && v.Clos? && wf(n, G, T) && exists Gc :: wfenv(n, v.H, Gc) && typ(n, context.Extend(v.mx, T.T1, Gc), v.mf, T.T2) && sub(n, Gc, T, G, T))
  || (T.TVal? && v.Clos? && vtyp(n, G, v.field, T.Tv))
  || (T.TTyp? && v.Clos? && wf(n, G, T.T))
  || (n>0 && exists T1 :: sub(n-1, G, T1, G, T) && vtyp(n-1, G, v, T1))
}

//
// Machinery
//

// Boilerplate monotonicity helpers.
ghost method monotonic_eval(n: nat, H: heap, t: tm)
  requires eval(n, H, t).Result?;
  ensures eval(n+1, H, t).Result? && eval(n+1, H, t).get==eval(n, H, t).get;
{
  if (t.tapp?) {
    var o := t.f;
    var a := t.a;
    monotonic_eval(n, H, o);
    monotonic_eval(n, H, a);
    var vo := eval(n+1, H, o);
    var va := eval(n+1, H, a);
    assert vo.get.Clos?;
    monotonic_eval(n-1, heap.Extend(vo.get.mx, va.get, vo.get.H), vo.get.mf);
  }
}
ghost method monotonic_path_eval(n: nat, G: context, x: int, T: ty)
  requires path_eval(n, G, x, T);
  ensures path_eval(n+1, G, x, T);
{
  monotonic_wf(n-1, G, T);
}
ghost method monotonic_wf(n: nat, G: context, T: ty)
  requires wf(n, G, T);
  ensures wf(n+1, G, T);
{
  if (T.TSel?) {
    var Tx :| path_eval(n-1, G, T.x, Tx);
    monotonic_path_eval(n-1, G, T.x, Tx);
  }
}
ghost method monotonic_sub(n: nat, G1: context, T1: ty, G2: context, T2: ty)
  requires sub(n, G1, T1, G2, T2);
  ensures sub(n+1, G1, T1, G2, T2);
{
  monotonic_sub_rec(n, G1, T1, G2, T2, true);
}
ghost method monotonic_sub_rec(n: nat, G1: context, T1: ty, G2: context, T2: ty, p: bool)
  requires sub_rec(n, G1, T1, G2, T2, p);
  ensures sub_rec(n+1, G1, T1, G2, T2, p);
  decreases n, if (p) then T1 else T2;
{
  if (T1.TArrow? && T2.TArrow?) {
    monotonic_sub_rec(n, G2, T2.T1, G1, T1.T1, !p);
    monotonic_sub_rec(n, G1, T1.T2, G2, T2.T2, p);
  } else if (n>0 && T1.TSel? && exists T1x :: path_eval(n, G1, T1.x, T1x) && sub_rec(n-1, G1, T1x, G2, T2, p)) {
    var T1x :| path_eval(n, G1, T1.x, T1x) && sub_rec(n-1, G1, T1x, G2, T2, p);
    monotonic_path_eval(n, G1, T1.x, T1x);
    monotonic_sub_rec(n-1, G1, T1x, G2, T2, p);
  } else if (n>0 && T2.TSel? && exists T2x :: path_eval(n, G2, T2.x, T2x) && sub_rec(n-1, G1, T1, G2, T2x, p)) {
    var T2x :| path_eval(n, G2, T2.x, T2x) && sub_rec(n-1, G1, T1, G2, T2x, p);
    monotonic_path_eval(n, G2, T2.x, T2x);
    monotonic_sub_rec(n-1, G1, T1, G2, T2x, p);
  }
}
ghost method help_typ_tnew(n: nat, G: context, t: tm, T: ty, TA1: ty, TA2: ty, Tv: ty)
  requires t.tnew? &&
      typ(n, context.Extend(t.mx, TA1, G), t.mf, TA2) && typ(n, G, t.field, Tv) &&
      wf(n, G, t.T) &&
      wf(n, G, TArrow(TA1, TA2)) &&
      ((T.TArrow? && T.T1==TA1 && T.T2==TA2) ||
       (T.TVal? && T.Tv==Tv) ||
       (T.TTyp? && T.T==t.T));
  ensures typ(n, G, t, T);
{
}
ghost method monotonic_typ(n: nat, G: context, t: tm, T: ty)
  requires typ(n, G, t, T);
  ensures typ(n+1, G, t, T);
  decreases n, t;
{
  if (t.tvar? && ty_lookup(t.x, G)==Result(T) && wf(n, G, T)) {
    monotonic_wf(n, G, T);
  }
  else if (t.tnew? &&
    exists TA1, TA2, Tv ::
      typ(n, context.Extend(t.mx, TA1, G), t.mf, TA2) && typ(n, G, t.field, Tv) &&
      wf(n, G, t.T) &&
      wf(n, G, TArrow(TA1, TA2)) &&
      ((T.TArrow? && T.T1==TA1 && T.T2==TA2) ||
       (T.TVal? && T.Tv==Tv) ||
       (T.TTyp? && T.T==t.T))) {
    var TA1, TA2, Tv :|
      typ(n, context.Extend(t.mx, TA1, G), t.mf, TA2) && typ(n, G, t.field, Tv) &&
      wf(n, G, t.T) &&
      wf(n, G, TArrow(TA1, TA2)) &&
      ((T.TArrow? && T.T1==TA1 && T.T2==TA2) ||
       (T.TVal? && T.Tv==Tv) ||
       (T.TTyp? && T.T==t.T));
    monotonic_typ(n, context.Extend(t.mx, TA1, G), t.mf, TA2);
    monotonic_typ(n, G, t.field, Tv);
    monotonic_wf(n, G, t.T);
    monotonic_wf(n, G, TArrow(TA1, TA2));
    help_typ_tnew(n+1, G, t, T, TA1, TA2, Tv);
  }
  else if (n>0 && exists T1 :: sub(n-1, G, T1, G, T) && typ(n-1, G, t, T1)) {
    var T1 :| sub(n-1, G, T1, G, T) && typ(n-1, G, t, T1);
    monotonic_sub(n-1, G, T1, G, T);
    monotonic_typ(n-1, G, t, T1);
  }
}
ghost method monotonic_wfenv(n: nat, H: heap, G: context)
  requires wfenv(n, H, G);
  ensures wfenv(n+1, H, G);
  decreases n, H, 0;
{
  forall (x | vl_lookup(x, H).Result?)
  ensures ty_lookup(x, G).Result? && vtyp(n+1, G, vl_lookup(x, H).get, ty_lookup(x, G).get);
  {
    monotonic_vtyp(n, G, vl_lookup(x, H).get, ty_lookup(x, G).get);
  }
}
ghost method monotonic_vtyp(n: nat, G: context, v: vl, T: ty)
  requires vtyp(n, G, v, T);
  ensures vtyp(n+1, G, v, T);
  decreases n, v;
{
  if (T.TArrow? && v.Clos? && wf(n, G, T) && exists Gc :: wfenv(n, v.H, Gc) && typ(n, context.Extend(v.mx, T.T1, Gc), v.mf, T.T2) && sub(n, Gc, T, G, T)) {
    monotonic_wf(n, G, T);
    var Gc :| wfenv(n, v.H, Gc) && typ(n, context.Extend(v.mx, T.T1, Gc), v.mf, T.T2) && sub(n, Gc, T, G, T);
    monotonic_wfenv(n, v.H, Gc);
    monotonic_typ(n, context.Extend(v.mx, T.T1, Gc), v.mf, T.T2);
    monotonic_sub(n, Gc, T, G, T);
  }
  else if (T.TTyp? && v.Clos? && wf(n, G, T.T)) {
    monotonic_wf(n, G, T.T);
  }
  else if (n>0 && exists T1 :: sub(n-1, G, T1, G, T) && vtyp(n-1, G, v, T1)) {
    var T1 :| sub(n-1, G, T1, G, T) && vtyp(n-1, G, v, T1);
    monotonic_sub(n-1, G, T1, G, T);
    monotonic_vtyp(n-1, G, v, T1);
  }
}
ghost method monotonic_plus_eval(m: nat, n: nat, H: heap, t: tm)
  requires m<=n;
  requires eval(m, H, t).Result?;
  ensures eval(n, H, t).Result? && eval(n, H, t).get==eval(m, H, t).get;
  decreases n-m;
{
  if (m<n) {
    monotonic_eval(m, H, t);
    monotonic_plus_eval(m+1, n, H, t);
  }
}
ghost method monotonic_plus_path_eval(m: nat, n: nat, G: context, x: int, T: ty)
  requires m<=n;
  requires path_eval(m, G, x, T);
  ensures path_eval(n, G, x, T);
  decreases n-m;
{
  if (m<n) {
    monotonic_path_eval(m, G, x, T);
    monotonic_plus_path_eval(m+1, n, G, x, T);
  }
}
ghost method monotonic_plus_wf(m: nat, n: nat, G: context, T: ty)
  requires m<=n;
  requires wf(m, G, T);
  ensures wf(n, G, T);
  decreases n-m;
{
  if (m<n) {
    monotonic_wf(m, G, T);
    monotonic_plus_wf(m+1, n, G, T);
  }
}
ghost method monotonic_plus_sub(m: nat, n: nat, G1: context, T1: ty, G2: context, T2: ty)
  requires m<=n;
  requires sub(m, G1, T1, G2, T2);
  ensures sub(n, G1, T1, G2, T2);
  decreases n-m;
{
  if (m<n) {
    monotonic_sub(m, G1, T1, G2, T2);
    monotonic_plus_sub(m+1, n, G1, T1, G2, T2);
  }
}
ghost method monotonic_plus_sub_rec(m: nat, n: nat, G1: context, T1: ty, G2: context, T2: ty, p: bool)
  requires m<=n;
  requires sub_rec(m, G1, T1, G2, T2, p);
  ensures sub_rec(n, G1, T1, G2, T2, p);
  decreases n-m;
{
  if (m<n) {
    monotonic_sub_rec(m, G1, T1, G2, T2, p);
    monotonic_plus_sub_rec(m+1, n, G1, T1, G2, T2, p);
  }
}
ghost method monotonic_plus_typ(m: nat, n: nat, G: context, t: tm, T: ty)
  requires m<=n;
  requires typ(m, G, t, T);
  ensures typ(n, G, t, T);
  decreases n-m;
{
  if (m<n) {
    monotonic_typ(m, G, t, T);
    monotonic_plus_typ(m+1, n, G, t, T);
  }
}
ghost method monotonic_plus_wfenv(m: nat, n: nat, H: heap, G: context)
  requires m<=n;
  requires wfenv(m, H, G);
  ensures wfenv(n, H, G);
  decreases n-m;
{
  if (m<n) {
    monotonic_wfenv(m, H, G);
    monotonic_plus_wfenv(m+1, n, H, G);
  }
}
ghost method monotonic_plus_vtyp(m: nat, n: nat, G: context, v: vl, T: ty)
  requires m<=n;
  requires vtyp(m, G, v, T);
  ensures vtyp(n, G, v, T);
  decreases n-m;
{
  if (m<n) {
    monotonic_vtyp(m, G, v, T);
    monotonic_plus_vtyp(m+1, n, G, v, T);
  }
}

//
// Properties
//

// Subtyping properties
ghost method lemma_sub_rec_refl(n: nat, G: context, T: ty, p: bool) returns (ns: nat)
  requires wf(n, G, T);
  ensures sub_rec(ns, G, T, G, T, p);
  decreases n, T;
{
  match T {
    case TInt => ns := 0;
    case Top  => ns := 0;
    case Bot  => ns := 0;
    case TArrow(T1, T2) =>
      var ns1 := lemma_sub_rec_refl(n, G, T1, !p);
      var ns2 := lemma_sub_rec_refl(n, G, T2, p);
      ns := ns1+ns2;
      monotonic_plus_sub_rec(ns1, ns, G, T1, G, T1, !p);
      monotonic_plus_sub_rec(ns2, ns, G, T2, G, T2, p);
    case TVal(Tv) =>
      var nsv := lemma_sub_rec_refl(n, G, Tv, p);
      ns := nsv;
    case TTyp(Tt) =>
      var nst := lemma_sub_rec_refl(n, G, Tt, p);
      ns := nst;
    case TSel(x) =>
      var Tx :| path_eval(n-1, G, x, Tx);
      monotonic_path_eval(n-1, G, x, Tx);
      var nx := lemma_sub_rec_refl(n-1, G, Tx, p);
      ns := n+nx;
      monotonic_plus_sub_rec(nx, ns, G, Tx, G, Tx, p);
      monotonic_plus_path_eval(n, ns+1, G, x, Tx);
      monotonic_path_eval(ns+1, G, x, Tx);
      ns := ns+2;
  }
}

ghost method {:timeLimit 50} lemma_sub_rec_trans(n12: nat, n23: nat, G1: context, T1: ty, G2: context, T2: ty, G3: context, T3: ty, p: bool) returns (n13: nat)
  requires sub_rec(n12, G1, T1, G2, T2, p);
  requires sub_rec(n23, G2, T2, G3, T3, p);
  ensures sub_rec(n13, G1, T1, G3, T3, p);
  decreases if p then n12 else n23, if p then n23 else n12, if p then T1 else T3, T2, if p then T3 else T1;
{
  n13 := 0;
  if (T1.TArrow? && T2.TArrow? && T3.TArrow?) {
    var ns1 := lemma_sub_rec_trans(n23, n12, G3, T3.T1, G2, T2.T1, G1, T1.T1, !p);
    var ns2 := lemma_sub_rec_trans(n12, n23, G1, T1.T2, G2, T2.T2, G3, T3.T2, p);
    n13 := ns1+ns2;
    monotonic_plus_sub_rec(ns1, n13, G3, T3.T1, G1, T1.T1, !p);
    monotonic_plus_sub_rec(ns2, n13, G1, T1.T2, G3, T3.T2, p);
  }
  else if (T1.TVal? && T2.TVal? && T3.TVal?) {
    var nr := lemma_sub_rec_trans(n12, n23, G1, T1.Tv, G2, T2.Tv, G3, T3.Tv, p);
    n13 := nr;
  }
  else if (T1.TTyp? && T2.TTyp? && T3.TTyp?) {
    var nr := lemma_sub_rec_trans(n12, n23, G1, T1.T, G2, T2.T, G3, T3.T, p);
    n13 := nr;
  }
  else if (n12>0 && T1.TSel? && exists T1x :: path_eval(n12, G1, T1.x, T1x) && sub_rec(n12-1, G1, T1x, G2, T2, p)) {
    var T1x :| path_eval(n12, G1, T1.x, T1x);
    var nr := lemma_sub_rec_trans(n12-1, n23, G1, T1x, G2, T2, G3, T3, p);
    n13 := n12+nr;
    monotonic_plus_path_eval(n12, n13+1, G1, T1.x, T1x);
    monotonic_plus_sub_rec(nr, n13, G1, T1x, G3, T3, p);
    n13 := n13+1;
  }
  else if (n23>0 && T3.TSel? && exists T3x :: path_eval(n23, G3, T3.x, T3x) && sub_rec(n23-1, G2, T2, G3, T3x, p)) {
    var T3x :| path_eval(n23, G3, T3.x, T3x);
    var nr := lemma_sub_rec_trans(n12, n23-1, G1, T1, G2, T2, G3, T3x, p);
    n13 := n23+nr;
    monotonic_plus_path_eval(n23, n13+1, G3, T3.x, T3x);
    monotonic_plus_sub_rec(nr, n13, G1, T1, G3, T3x, p);
    n13 := n13+1;
  }
  else if (n12>0 && n23>0 && T2.TSel? && exists T2x :: path_eval(n12, G2, T2.x, T2x) && sub_rec(n12-1, G1, T1, G2, T2x, p) && sub_rec(n23-1, G2, T2x, G3, T3, p)) {
    var T2x :| path_eval(n12, G2, T2.x, T2x);
    var nr := lemma_sub_rec_trans(n12-1, n23-1, G1, T1, G2, T2x, G3, T3, p);
    n13 := nr;
  }
}

/*
// Hints
ghost method hint_vtyp_rec_sub(ns: nat, nt: nat, nw: nat, G: context, v: vl, T1: ty, T: ty) returns (nv: nat)
  requires wf(nw, G, T);
  requires sub(ns, G, T1, G, T);
  requires vtyp_rec(nt, G, v, T1);
  ensures vtyp_rec(nv, G, v, T);
{
  var nr := ns+nt+nw;
  help_sub_rec_monotonic_plus(ns, nr, G, T1, G, T, true);
  help_vtyp_rec_monotonic_plus(nt, nr, G, v, T1);
  assert sub(nr, G, T1, G, T) && vtyp_rec(nr, G, v, T1);
  help_wf_monotonic_plus(nw, nr+1, G, T);
  nv := nr+1;
}
ghost method hint_vtyp_rec_arrow(n: nat, nw: nat, G: context, v: vl, T: ty) returns (nv: nat)
  requires wf(nw, G, T);
  requires T.TArrow?;
  requires typ(n, context.Extend(v.mx, T.T1, G), v.mf, T.T2);
  ensures vtyp_rec(nv, G, v, T);
{
  nv := nw+n;
  help_wf_monotonic_plus(nw, nv, G, T);
  help_typ_monotonic_plus(n, nv, context.Extend(v.mx, T.T1, G), v.mf, T.T2);
}

// Inversions

ghost method inv_typ_var(n: nat, G: context, x: int, T: ty) returns (nv: nat)
  requires typ(n, G, tvar(x), T);
  ensures ty_lookup(x, G).Result?;
  ensures sub(nv, G, ty_lookup(x, G).get, G, T);
{
  if (ty_lookup(x, G)==Result(T)) {
    var nr := lemma_sub_rec_refl(n, G, T, true);
    nv := nr;
  }
  else if (n>0 && exists T' :: sub(n-1, G, T', G, T) && typ(n-1, G, tvar(x), T')) {
    var T' :| sub(n-1, G, T', G, T) && typ(n-1, G, tvar(x), T');
    var nr := inv_typ_var(n-1, G, x, T');
    var ns := lemma_sub_rec_trans(nr, n-1, G, ty_lookup(x, G).get, G, T', G, T, true);
    nv := ns;
  }
}

ghost method inv_typ_get(ntyp: nat, G: context, o: tm, T: ty) returns (nv: nat, T': ty)
  requires typ(ntyp, G, tget(o), T);
  ensures typ(nv, G, o, TVal(T'));
  ensures sub(nv, G, T', G, T);
{
  if (typ(ntyp, G, o, TVal(T))) {
    T' := T;
    var ns := lemma_sub_rec_refl(ntyp, G, T, true);
    nv := ns+ntyp;
    help_sub_rec_monotonic_plus(ns, nv, G, T, G, T, true);
    help_typ_monotonic_plus(ntyp, nv, G, o, TVal(T'));
  }
  else if (ntyp>0 && exists T1 :: sub(ntyp-1, G, T1, G, T) && typ(ntyp-1, G, tget(o), T1)) {
    var T1 :| sub(ntyp-1, G, T1, G, T) && typ(ntyp-1, G, tget(o), T1);
    var nr, T'_ := inv_typ_get(ntyp-1, G, o, T1);
    T' := T'_;
    var ns := lemma_sub_rec_trans(nr, ntyp-1, G, T', G, T1, G, T, true);
    nv := ns+nr;
    help_sub_rec_monotonic_plus(ns, nv, G, T', G, T, true);
    help_typ_monotonic_plus(nr, nv, G, o, TVal(T'));
  }
}

ghost method inv_typ_app(n: nat, G: context, f: tm, a: tm, T: ty) returns (nv: nat, T1: ty, T2: ty)
  requires typ(n, G, tapp(f, a), T);
  ensures typ(nv, G, f, TArrow(T1, T2));
  ensures typ(nv, G, a, T1);
  ensures sub(nv, G, T2, G, T);
{
  if (exists T1 :: typ(n, G, a, T1) && typ(n, G, f, TArrow(T1, T))) {
    var T1_ :| typ(n, G, a, T1_) && typ(n, G, f, TArrow(T1_, T));
    T1 := T1_;
    T2 := T;
    assert wf(n, G, T);
    var ns := lemma_sub_rec_refl(n, G, T, true);
    nv := ns+n;
    help_sub_rec_monotonic_plus(ns, nv, G, T, G, T, true);
    help_typ_monotonic_plus(n, nv, G, a, T1_);
    help_typ_monotonic_plus(n, nv, G, f, TArrow(T1_, T));
  } else if (n>0 && exists T_ :: sub(n-1, G, T_, G, T) && typ(n-1, G, tapp(f, a), T_)) {
    var T_ :| sub(n-1, G, T_, G, T) && typ(n-1, G, tapp(f, a), T_);
    var n_, T1_, T2_ := inv_typ_app(n-1, G, f, a, T_);
    T1 := T1_;
    T2 := T2_;
    var nt := lemma_sub_rec_trans(n_, n-1, G, T2, G, T_, G, T, true);
    nv := nt+n_;
    help_sub_rec_monotonic_plus(nt, nv, G, T2, G, T, true);
    help_typ_monotonic_plus(n_, nv, G, a, T1);
    help_typ_monotonic_plus(n_, nv, G, f, TArrow(T1, T2));
  }
}

ghost method inv_wf_val(n: nat, nw: nat, G: context, v: vl, Tv: ty) returns (nv: nat, Tv': ty)
  requires wf(nw, G, Tv);
  requires vtyp_rec(n, G, v, TVal(Tv));
  ensures v.field.Some?;
  ensures vtyp_rec(nv, G, v.field.get, Tv');
  ensures sub(nv, G, Tv', G, Tv);
  ensures wf(nv, G, Tv');
{
  var T := TVal(Tv);
  var ns := lemma_sub_rec_refl(nw, G, T, true);
  nv, Tv' := inv_sub_val(n, ns, G, v, Tv, T);
}

ghost method inv_sub_val(n: nat, ns: nat, G: context, v: vl, Tv: ty, T: ty) returns (nv: nat, Tv': ty)
  requires sub(ns, G, T, G, TVal(Tv));
  requires vtyp_rec(n, G, v, T);
  ensures v.field.Some?;
  ensures vtyp_rec(nv, G, v.field.get, Tv');
  ensures sub(nv, G, Tv', G, Tv);
  ensures wf(nv, G, Tv');
{
  if (T.TVal? && v.field.Some? && vtyp_rec(n, G, v.field.get, T.Tv)) {
    Tv' := T.Tv;
    nv := n+ns;
    help_sub_rec_monotonic_plus(ns, nv, G, T, G, TVal(Tv), true);
    help_vtyp_rec_monotonic_plus(n, nv, G, v.field.get, T.Tv);
  }
  else if (n>0 && exists T' :: sub(n-1, G, T', G, T) && vtyp_rec(n-1, G, v, T')) {
    var T' :| sub(n-1, G, T', G, T) && vtyp_rec(n-1, G, v, T');
    var ns' := lemma_sub_rec_trans(n-1, ns, G, T', G, T, G, TVal(Tv), true);
    nv, Tv' := inv_sub_val(n-1, ns', G, v, Tv, T');
  }
}

ghost method inv_wf_arrow(n: nat, nw: nat, G: context, v: vl, T1: ty, T2: ty) returns (nv: nat, T1': ty, T2': ty)
  requires wf(nw, G, TArrow(T1, T2));
  requires vtyp_rec(n, G, v, TArrow(T1, T2));
  ensures typ(nv, context.Extend(v.mx, T1', G), v.mf, T2');
  ensures sub(nv, G, TArrow(T1', T2'), G, TArrow(T1, T2));
  ensures wf(nv, G, TArrow(T1', T2'));
{
  var T := TArrow(T1, T2);
  var ns := lemma_sub_rec_refl(nw, G, T, true);
  nv, T1', T2' := inv_sub_arrow(n, ns, G, v, T1, T2, T);
}

ghost method inv_sub_arrow(n: nat, ns: nat, G: context, v: vl, T1: ty, T2: ty, T: ty) returns (nv: nat, T1': ty, T2': ty)
  requires sub(ns, G, T, G, TArrow(T1, T2));
  requires vtyp_rec(n, G, v, T);
  ensures typ(nv, context.Extend(v.mx, T1', G), v.mf, T2');
  ensures sub(nv, G, TArrow(T1', T2'), G, TArrow(T1, T2));
  ensures wf(nv, G, TArrow(T1', T2'));
{
  if (T.TArrow? && typ(n, context.Extend(v.mx, T.T1, G), v.mf, T.T2)) {
    T1' := T.T1;
    T2' := T.T2;
    nv := ns+n;
    help_wf_monotonic_plus(n, nv, G, T);
    help_sub_rec_monotonic_plus(ns, nv, G, TArrow(T1', T2'), G, TArrow(T1, T2), true);
    help_typ_monotonic_plus(n, nv, context.Extend(v.mx, T1', G), v.mf, T2');
  }
  else if (n>0 && exists T' :: sub(n-1, G, T', G, T) && vtyp_rec(n-1, G, v, T')) {
    var T' :| sub(n-1, G, T', G, T) && vtyp_rec(n-1, G, v, T');
    var ns' := lemma_sub_rec_trans(n-1, ns, G, T', G, T, G, TArrow(T1, T2), true);
    nv, T1', T2' := inv_sub_arrow(n-1, ns', G, v, T1, T2, T');
  }
}

// Type-safety properties
ghost method lemma_lookup_safe(n: nat, H: heap, G: context, x: int)
  requires wfenv(n, H, G);
  requires ty_lookup(x, G).Result?;
  requires vl_lookup(x, H).Result?;
  ensures vtyp_rec(n, G, vl_lookup(x, H).get, ty_lookup(x, G).get);
{
}

ghost method lemma_eval_safe(ntyp: nat, nev: nat, nenv: nat, H: heap, G: context, t: tm, T: ty) returns (nv: nat)
  requires typ(ntyp, G, t, T);
  requires wfenv(nenv, H, G);
  // TODO(namin): We should ensure that if a term is well-typed, then it doesn't get stuck!
  //              It is not enough to check that if it's a result, it has the correct type...
  requires eval(nev, H, t).Result?;
  ensures vtyp_rec(nv, G, eval(nev, H, t).get, T);
  decreases nev, t, ntyp;
{
  var v := eval(nev, H, t).get;
  match t {
  case tvar(x) =>
    var ni := inv_typ_var(ntyp, G, x, T);
    lemma_lookup_safe(nenv, H, G, x);
    assert vtyp_rec(nenv, G, vl_lookup(x, H).get, ty_lookup(x, G).get);
    assert sub(ni, G, ty_lookup(x, G).get, G, T) && vtyp_rec(nenv, G, v, ty_lookup(x, G).get);
    nv := hint_vtyp_rec_sub(ni, nenv, ntyp, G, v, ty_lookup(x, G).get, T);
  case tapp(f, a) =>
    var ni, T1, T2 := inv_typ_app(ntyp, G, f, a, T);
    var nf := lemma_eval_safe(ni, nev, nenv, H, G, f, TArrow(T1, T2));
    var na := lemma_eval_safe(ni, nev, nenv, H, G, a, T1);
    var vf := eval(nev, H, f).get;
    var va := eval(nev, H, a).get;
    var nfi, T1', T2' := inv_wf_arrow(nf, nf, G, vf, T1, T2);
    var G' := context.Extend(vf.mx, T1', G);
    var H' := heap.Extend(vf.mx, va, H);
    assume wfenv(nenv, H', G'); // TODO(namin): This one should be a formality.
    var nr := lemma_eval_safe(nfi, nev-1, nenv, H', G', vf.mf, T2');
    assert vtyp_rec(nr, G', eval(nev, H, t).get, T2');
    assume vtyp_rec(nr, G, eval(nev, H, t).get, T2'); // TODO(namin): I am not sure about this. The heap does grow with the computation.
    var nt := lemma_sub_rec_trans(nfi, ni, G, T2', G, T2, G, T, true);
    nv := hint_vtyp_rec_sub(nt, nr, ntyp, G, v, T2', T);
  case tnew(mx, mf, tv, Tt) =>
    if (T.TArrow? && typ(ntyp, context.Extend(t.mx, T.T1, G), t.mf, T.T2)) {
      nv := hint_vtyp_rec_arrow(ntyp, ntyp, G, v, T);
    }
    else if (T.TVal? && t.field.Some? && typ(ntyp, G, t.field.get, T.Tv)) {
      nv := lemma_eval_safe(ntyp, nev, nenv, H, G, t.field.get, T.Tv);
    }
    else if (ntyp>0 && exists T1 :: sub(ntyp-1, G, T1, G, T) && typ(ntyp-1, G, t, T1)) {
      var T1 :| sub(ntyp-1, G, T1, G, T) && typ(ntyp-1, G, t, T1);
      var nr := lemma_eval_safe(ntyp-1, nev, nenv, H, G, t, T1);
      nv := hint_vtyp_rec_sub(ntyp-1, nr, ntyp, G, v, T1, T);
    }
    else {}
  case tget(o) =>
    var ni, T' := inv_typ_get(ntyp, G, o, T);
    var nr := lemma_eval_safe(ni, nev, nenv, H, G, o, TVal(T'));
    var vo := eval(nev, H, o).get;
    var nvi, Tv := inv_wf_val(nr, nr, G, vo, T');
    var nt := lemma_sub_rec_trans(nvi, ni, G, Tv, G, T', G, T, true);
    nv := hint_vtyp_rec_sub(nt, nvi, ntyp, G, v, Tv, T);
  }
}
*/