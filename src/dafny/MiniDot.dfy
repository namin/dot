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
  wf(n, G, T) && (
     (t.tvar? && ty_lookup(t.x, G)==Result(T))
  || (t.tnew? && T.TArrow? && typ(n, context.Extend(t.mx, T.T1, G), t.mf, T.T2))
  || (t.tnew? && T.TVal? && t.field.Some? && typ(n, G, t.field.get, T.Tv))
  || (t.tnew? && T.TTyp? && t.T==T.T)
  || (t.tapp? && exists T1 :: typ(n, G, t.a, T1) && typ(n, G, t.f, TArrow(T1, T)))
  || (t.tget? && typ(n, G, t.o, TVal(T)))
  || (n>0 && exists T1 :: sub(n-1, G, T1, G, T) && typ(n-1, G, t, T1)))
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
  wf(n, G, T) && (
     (T.TArrow? && typ(n, context.Extend(v.mx, T.T1, G), v.mf, T.T2))
  || (T.TVal? && v.field.Some? && vtyp(n, v.field.get, T.Tv))
  || (n>0 && exists T1 :: sub(n-1, G, T1, G, T) && vtyp_rec(n-1, G, v, T1)))
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

// Boilerplate monotonicity helpers.
ghost method help_sub_rec_monotonic(n: nat, G1: context, T1: ty, G2: context, T2: ty, p: bool)
  requires sub_rec(n, G1, T1, G2, T2, p);
  ensures sub_rec(n+1, G1, T1, G2, T2, p);
  decreases n, if (p) then T1 else T2;
{
  if (n>0 && T1.TSel? && ty_lookup(T1.x, G1).Result? && sub_rec(n-1, G1, ty_lookup(T1.x, G1).get, G2, T2, p)) {
    help_sub_rec_monotonic(n-1, G1, ty_lookup(T1.x, G1).get, G2, T2, p);
  }
}
ghost method help_typ_monotonic(n: nat, G: context, t: tm, T: ty)
  requires typ(n, G, t, T);
  ensures typ(n+1, G, t, T);
  decreases n, t;
{
  help_wf_monotonic(n, G, T);
  if (t.tvar? && ty_lookup(t.x, G)==Result(T)) {}
  else if (t.tnew? && T.TArrow? && typ(n, context.Extend(t.mx, T.T1, G), t.mf, T.T2)) {}
  else if (t.tnew? && T.TVal? && t.field.Some? && typ(n, G, t.field.get, T.Tv)) {
    help_typ_monotonic(n, G, t.field.get, T.Tv);
  }
  else if (t.tnew? && T.TTyp? && t.T==T.T) {}
  else if (t.tapp? && exists T1 :: typ(n, G, t.a, T1) && typ(n, G, t.f, TArrow(T1, T))) {}
  else if (t.tget? && typ(n, G, t.o, TVal(T))) {}
  else if (n>0 && exists T1 :: sub(n-1, G, T1, G, T) && typ(n-1, G, t, T1)) {
    var T1 :| sub(n-1, G, T1, G, T) && typ(n-1, G, t, T1);
    help_sub_rec_monotonic(n-1, G, T1, G, T, true);
  } else {}
}
ghost method help_wfenv_monotonic(n: nat, H: heap, G: context)
  requires wfenv(n, H, G);
  ensures wfenv(n+1, H, G);
  decreases H, n, 0;
{
  forall (x | vl_lookup(x, H).Result?)
  ensures ty_lookup(x, G).Result? && vtyp_rec(n+1, G, vl_lookup(x, H).get, ty_lookup(x, G).get);
  {
    help_vtyp_rec_monotonic(n, G, vl_lookup(x, H).get, ty_lookup(x, G).get);
  }
}
ghost method help_vtyp_monotonic(n: nat, v: vl, T: ty)
  requires vtyp(n, v, T);
  ensures vtyp(n+1, v, T);
  decreases v, n, 2;
{
  var G :| wfenv(n, v.H, G) && vtyp_rec(n, G, v, T);
  help_wfenv_monotonic(n, v.H, G);
  help_vtyp_rec_monotonic(n, G, v, T);
}
ghost method help_vtyp_rec_monotonic(n: nat, G: context, v: vl, T: ty)
  requires vtyp_rec(n, G, v, T);
  ensures vtyp_rec(n+1, G, v, T);
  decreases v, n, 1;
{
  help_wf_monotonic(n, G, T);
  if (T.TArrow? && typ(n, context.Extend(v.mx, T.T1, G), v.mf, T.T2)) {
    help_typ_monotonic(n, context.Extend(v.mx, T.T1, G), v.mf, T.T2);
  }
  else if (T.TVal? && v.field.Some? && vtyp(n, v.field.get, T.Tv)) {
     help_vtyp_monotonic(n, v.field.get, T.Tv);
  }
  else if (n>0 && exists T1 :: sub(n-1, G, T1, G, T) && vtyp_rec(n-1, G, v, T1)) {
    var T1 :| sub(n-1, G, T1, G, T) && vtyp_rec(n-1, G, v, T1);
    help_sub_rec_monotonic(n-1, G, T1, G, T, true);
  }
}
ghost method help_wf_monotonic(n: nat, G: context, T: ty)
  requires wf(n, G, T);
  ensures wf(n+1, G, T);
{
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
ghost method help_typ_monotonic_plus(m: nat, n: nat, G: context, t: tm, T: ty)
  requires typ(m, G, t, T);
  requires m<=n;
  ensures typ(n, G, t, T);
  decreases n-m;
{
  if (m<n) {
    help_typ_monotonic(m, G, t, T);
    help_typ_monotonic_plus(m+1, n, G, t, T);
  }
}
ghost method help_wfenv_monotonic_plus(m: nat, n: nat, H: heap, G: context)
  requires wfenv(m, H, G);
  requires m<=n;
  ensures wfenv(n, H, G);
  decreases n-m;
{
  if (m<n) {
    help_wfenv_monotonic(m, H, G);
    help_wfenv_monotonic_plus(m+1, n, H, G);
  }
}
ghost method help_vtyp_monotonic_plus(m: nat, n: nat, v: vl, T: ty)
  requires vtyp(m, v, T);
  requires m<=n;
  ensures vtyp(n, v, T);
  decreases n-m;
{
  if (m<n) {
    help_vtyp_monotonic(m, v, T);
    help_vtyp_monotonic_plus(m+1, n, v, T);
  }
}
ghost method help_vtyp_rec_monotonic_plus(m: nat, n: nat, G: context, v: vl, T: ty)
  requires vtyp_rec(m, G, v, T);
  requires m<=n;
  ensures vtyp_rec(n, G, v, T);
  decreases n-m;
{
  if (m<n) {
    help_vtyp_rec_monotonic(m, G, v, T);
    help_vtyp_rec_monotonic_plus(m+1, n, G, v, T);
  }
}
ghost method help_wf_monotonic_plus(m: nat, n: nat, G: context, T: ty)
  requires wf(m, G, T);
  requires m<=n;
  ensures wf(n, G, T);
  decreases n-m;
{
  if (m<n) {
    help_wf_monotonic(m, G, T);
    help_wf_monotonic_plus(m+1, n, G, T);
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

ghost method inv_wf_arrow(n: nat, nw: nat, G: context, v: vl, T1: ty, T2: ty) returns (nv: nat, T1': ty, T2': ty)
  requires wf(nw, G, TArrow(T1, T2));
  requires vtyp_rec(n, G, v, TArrow(T1, T2));
  ensures typ(nv, context.Extend(v.mx, T1', G), v.mf, T2');
  ensures sub(nv, G, TArrow(T1', T2'), G, TArrow(T1, T2));
  ensures wf(nv, G, TArrow(T1', T2'));
{
  var T := TArrow(T1, T2);
  var ns := lemma_sub_rec_refl(nw, G, T, true);
  nv, T1', T2' := inv_sub_arrow(n, ns, nw, G, v, T1, T2, T);
}

ghost method inv_sub_arrow(n: nat, ns: nat, nw: nat, G: context, v: vl, T1: ty, T2: ty, T: ty) returns (nv: nat, T1': ty, T2': ty)
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
    nv, T1', T2' := inv_sub_arrow(n-1, ns', nw, G, v, T1, T2, T');
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
  requires eval(nev, H, t).Result?;
  ensures vtyp_rec(nv, G, eval(nev, H, t).get, T);
  decreases nev, t;
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
    assume wfenv(nenv, H', G'); // TODO
    var nr := lemma_eval_safe(nfi, nev-1, nenv, H', G', vf.mf, T2');
    assume vtyp_rec(nr, G, eval(nev, H, t).get, T2'); // TODO
    var nt := lemma_sub_rec_trans(nfi, ni, G, T2', G, T2, G, T, true);
    nv := hint_vtyp_rec_sub(nt, nr, ntyp, G, v, T2', T);
  case tnew(mx, mf, tv, Tt) =>
    assume vtyp_rec(nv, G, eval(nev, H, t).get, T);
  case tget(o) =>
    assume vtyp_rec(nv, G, eval(nev, H, t).get, T);
  }
}
