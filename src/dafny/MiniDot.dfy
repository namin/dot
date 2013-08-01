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
            | tvar(x: nat)                                 // x                                            (variable)
            | tnew(mf: tm, field: tm, T: ty)               // new { def apply(x)=t1; val get=t2; type T }  (object/function creation)
            | tapp(f: tm, a: tm)                           // t.apply(t)                                   (method call)
            | tget(o: tm)                                  // t.get                                        (field selection)
            ;

datatype ty = Top | Bot | TInt
            | TArrow(T1: ty, T2: ty)                       // { T1 => T2 }                                 (method)
            | TVal(Tv: ty)                                 // { val T }                                    (field member)
            | TTyp(T: ty)                                  // { type T }                                   (type member)
            | TSel(x: nat)                                 // x.T                                          (type selection)
            ;

// G (type  env)
// H (value env)
function lookup<A>(k: nat, s: seq<A>): result<A>
  ensures lookup(k, s).Result? ==> k<|s| && lookup(k, s).get==s[k];
  ensures k<|s| ==> lookup(k, s).Result? && lookup(k, s).get==s[k];
{
  if (k<|s|) then Result(s[k]) else Stuck
}
function extend<A>(v: A, s: seq<A>): seq<A>
  ensures |extend(v, s)|==|s|+1;
{
  s+[v]
}

datatype vl = Num(n: int)                               // n                                    (constant number)
            | Clos(H: seq<vl>, mf: tm, field: vl)       // Clos H { def apply(x)=t; val get=v } (object/closure)

// Dynamic Semantics            
function eval(n: nat, H: seq<vl>, t: tm): result<vl>
  decreases n, t;
{
  match t
  case tnum(n) => Result(Num(n))
  case tvar(x) => lookup(x, H)
  case tnew(mf, t, T) =>
    var v := eval(n, H, t);
    if !v.Result? then v else
    Result(Clos(H, mf, v.get))
  case tapp(o, a) =>
    var vo := eval(n, H, o);
    var va := eval(n, H, a);
    if !vo.Result? || !va.Result? then chain(vo, va) else
    if n==0 then TimeOut else
    if !vo.get.Clos? then Stuck else
    eval(n-1, extend(va.get, vo.get.H), vo.get.mf)
  case tget(o) =>
    var vo := eval(n, H, o);
    if !vo.Result? then vo else
    if !vo.get.Clos? then Stuck else
    Result(vo.get.field)
}

// Static Semantics
predicate path_eval(n: nat, G: seq<ty>, x: nat, T: ty)
{
  n>0 && lookup(x, G).Result? && lookup(x, G).get==T && wf(n-1, G, T)
}

predicate wf(n: nat, G: seq<ty>, T: ty)
{
     (T.Top?)
  || (T.Bot?)
  || (T.TInt?)
  || (T.TArrow? && wf(n, G, T.T1) && wf(n, G, T.T2))
  || (T.TVal? && wf(n, G, T.Tv))
  || (T.TTyp? && wf(n, G, T.T))
  || (n>0 && T.TSel? && exists Tx :: path_eval(n-1, G, T.x, Tx))
}

predicate sub(n: nat, G1: seq<ty>, T1: ty, G2: seq<ty>, T2: ty)
{
  sub_rec(n, G1, T1, G2, T2, true)
}

predicate sub_rec(n: nat, G1: seq<ty>, T1: ty, G2: seq<ty>, T2: ty, p: bool)
  decreases n, if (p) then T1 else T2;
{
     (T1.TInt? && T2.TInt?)
  || (T2.Top? && wf(n, G1, T1))
  || (T1.Bot? && wf(n, G2, T2))
  || (T1.TArrow? && T2.TArrow? && sub_rec(n, G2, T2.T1, G1, T1.T1, !p) && sub_rec(n, G1, T1.T2, G2, T2.T2, p))
  || (T1.TVal? && T2.TVal? && sub_rec(n, G1, T1.Tv, G2, T2.Tv, p))
  || (T1.TTyp? && T2.TTyp? && sub_rec(n, G1, T1.T, G2, T2.T, p))
  || (n>0 && T1.TSel? && exists T1x :: path_eval(n, G1, T1.x, T1x) && sub_rec(n-1, G1, T1x, G2, T2, p))
  || (n>0 && T2.TSel? && exists T2x :: path_eval(n, G2, T2.x, T2x) && sub_rec(n-1, G1, T1, G2, T2x, p))
}

predicate typ(n: nat, G: seq<ty>, t: tm, T: ty)
  decreases n, t;
{
     (t.tnum? && T.TInt?)
  || (t.tvar? && lookup(t.x, G)==Result(T) && wf(n, G, T))
  || (t.tnew? &&
      exists TA1, TA2, Tv ::
      typ(n, extend(TA1, G), t.mf, TA2) && typ(n, G, t.field, Tv) &&
      wf(n, G, t.T) &&
      wf(n, G, TArrow(TA1, TA2)) &&
      ((T.TArrow? && T.T1==TA1 && T.T2==TA2) ||
       (T.TVal? && T.Tv==Tv) ||
       (T.TTyp? && T.T==t.T)))
  || (t.tapp? && exists T1 :: typ(n, G, t.a, T1) && typ(n, G, t.f, TArrow(T1, T)))
  || (t.tget? && typ(n, G, t.o, TVal(T)))
  || (n>0 && exists T1 :: sub(n-1, G, T1, G, T) && typ(n-1, G, t, T1))
}

predicate wfenv(n: nat, H: seq<vl>, G: seq<ty>)
  decreases n, H, 0;
{
  |H|==|G| && (
    forall x :: 0 <= x < |H| ==> vtyp(n, G[..x], H[x], G[x]))
}

predicate vtyp(n: nat, G: seq<ty>, v: vl, T: ty)
  decreases n, v;
{
     (T.TInt? && v.Num?)
  || (T.TArrow? && v.Clos? && wf(n, G, T) && exists Gc :: wfenv(n, v.H, Gc) && typ(n, extend(T.T1, Gc), v.mf, T.T2) && sub(n, Gc, T, G, T))
  || (T.TVal? && v.Clos? && vtyp(n, G, v.field, T.Tv))
  || (T.TTyp? && v.Clos? && wf(n, G, T.T))
  || (n>0 && exists G1, T1 :: sub(n-1, G1, T1, G, T) && vtyp(n-1, G1, v, T1))
}

//
// Machinery
//

// Boilerplate monotonicity helpers.
ghost method monotonic_eval(n: nat, H: seq<vl>, t: tm)
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
    monotonic_eval(n-1, extend(va.get, vo.get.H), vo.get.mf);
  }
}
ghost method monotonic_path_eval(n: nat, G: seq<ty>, x: nat, T: ty)
  requires path_eval(n, G, x, T);
  ensures path_eval(n+1, G, x, T);
{
  monotonic_wf(n-1, G, T);
}
ghost method monotonic_wf(n: nat, G: seq<ty>, T: ty)
  requires wf(n, G, T);
  ensures wf(n+1, G, T);
{
  if (T.TSel?) {
    var Tx :| path_eval(n-1, G, T.x, Tx);
    monotonic_path_eval(n-1, G, T.x, Tx);
  }
}
ghost method monotonic_sub(n: nat, G1: seq<ty>, T1: ty, G2: seq<ty>, T2: ty)
  requires sub(n, G1, T1, G2, T2);
  ensures sub(n+1, G1, T1, G2, T2);
{
  monotonic_sub_rec(n, G1, T1, G2, T2, true);
}
ghost method monotonic_sub_rec(n: nat, G1: seq<ty>, T1: ty, G2: seq<ty>, T2: ty, p: bool)
  requires sub_rec(n, G1, T1, G2, T2, p);
  ensures sub_rec(n+1, G1, T1, G2, T2, p);
  decreases n, if (p) then T1 else T2;
{
  if (T2.Top? && wf(n, G1, T1)) {
    monotonic_wf(n, G1, T1);
  } else if (T1.Bot? && wf(n, G2, T2)) {
    monotonic_wf(n, G2, T2);
  } else if (T1.TArrow? && T2.TArrow?) {
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
ghost method invariant_p_sub_rec(n: nat, G1: seq<ty>, T1: ty, G2: seq<ty>, T2: ty, p: bool)
  requires sub_rec(n, G1, T1, G2, T2, p);
  ensures sub_rec(n, G1, T1, G2, T2, !p);
  ensures sub(n, G1, T1, G2, T2);
  decreases n, if (p) then T1 else T2;
{
}
ghost method help_typ_tnew(n: nat, G: seq<ty>, t: tm, T: ty, TA1: ty, TA2: ty, Tv: ty)
  requires t.tnew? &&
      typ(n, extend(TA1, G), t.mf, TA2) && typ(n, G, t.field, Tv) &&
      wf(n, G, t.T) &&
      wf(n, G, TArrow(TA1, TA2)) &&
      ((T.TArrow? && T.T1==TA1 && T.T2==TA2) ||
       (T.TVal? && T.Tv==Tv) ||
       (T.TTyp? && T.T==t.T));
  ensures typ(n, G, t, T);
{
}
ghost method monotonic_typ(n: nat, G: seq<ty>, t: tm, T: ty)
  requires typ(n, G, t, T);
  ensures typ(n+1, G, t, T);
  decreases n, t;
{
  if (t.tvar? && lookup(t.x, G)==Result(T) && wf(n, G, T)) {
    monotonic_wf(n, G, T);
  }
  else if (t.tnew? &&
    exists TA1, TA2, Tv ::
      typ(n, extend(TA1, G), t.mf, TA2) && typ(n, G, t.field, Tv) &&
      wf(n, G, t.T) &&
      wf(n, G, TArrow(TA1, TA2)) &&
      ((T.TArrow? && T.T1==TA1 && T.T2==TA2) ||
       (T.TVal? && T.Tv==Tv) ||
       (T.TTyp? && T.T==t.T))) {
    var TA1, TA2, Tv :|
      typ(n, extend(TA1, G), t.mf, TA2) && typ(n, G, t.field, Tv) &&
      wf(n, G, t.T) &&
      wf(n, G, TArrow(TA1, TA2)) &&
      ((T.TArrow? && T.T1==TA1 && T.T2==TA2) ||
       (T.TVal? && T.Tv==Tv) ||
       (T.TTyp? && T.T==t.T));
    monotonic_typ(n, extend(TA1, G), t.mf, TA2);
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
ghost method monotonic_wfenv(n: nat, H: seq<vl>, G: seq<ty>)
  requires wfenv(n, H, G);
  ensures wfenv(n+1, H, G);
  decreases n, H, 0;
{
  forall (x | 0 <= x < |H|)
  ensures vtyp(n+1, G[..x], H[x], G[x]);
  {
    monotonic_vtyp(n, G[..x], H[x], G[x]);
  }
}
ghost method help_vtyp_sub(n: nat, G: seq<ty>, v: vl, T: ty, G1: seq<ty>, T1: ty)
  requires n>0;
  requires sub(n-1, G1, T1, G, T);
  requires vtyp(n-1, G1, v, T1);
  ensures vtyp(n, G, v, T);
{
}

ghost method monotonic_vtyp(n: nat, G: seq<ty>, v: vl, T: ty)
  requires vtyp(n, G, v, T);
  ensures vtyp(n+1, G, v, T);
  decreases n, v;
{
  if (T.TArrow? && v.Clos? && wf(n, G, T) && exists Gc :: wfenv(n, v.H, Gc) && typ(n, extend(T.T1, Gc), v.mf, T.T2) && sub(n, Gc, T, G, T)) {
    monotonic_wf(n, G, T);
    var Gc :| wfenv(n, v.H, Gc) && typ(n, extend(T.T1, Gc), v.mf, T.T2) && sub(n, Gc, T, G, T);
    monotonic_wfenv(n, v.H, Gc);
    monotonic_typ(n, extend(T.T1, Gc), v.mf, T.T2);
    monotonic_sub(n, Gc, T, G, T);
  }
  else if (T.TTyp? && v.Clos? && wf(n, G, T.T)) {
    monotonic_wf(n, G, T.T);
  }
  else if (n>0 && exists G1, T1 :: sub(n-1, G1, T1, G, T) && vtyp(n-1, G1, v, T1)) {
    var G1, T1 :| sub(n-1, G1, T1, G, T) && vtyp(n-1, G1, v, T1);
    monotonic_sub(n-1, G1, T1, G, T);
    monotonic_vtyp(n-1, G1, v, T1);
    help_vtyp_sub(n+1, G, v, T, G1, T1);
  }
}
ghost method monotonic_plus_eval(m: nat, n: nat, H: seq<vl>, t: tm)
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
ghost method monotonic_plus_path_eval(m: nat, n: nat, G: seq<ty>, x: nat, T: ty)
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
ghost method monotonic_plus_wf(m: nat, n: nat, G: seq<ty>, T: ty)
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
ghost method monotonic_plus_sub(m: nat, n: nat, G1: seq<ty>, T1: ty, G2: seq<ty>, T2: ty)
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
ghost method monotonic_plus_sub_rec(m: nat, n: nat, G1: seq<ty>, T1: ty, G2: seq<ty>, T2: ty, p: bool)
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
ghost method monotonic_plus_typ(m: nat, n: nat, G: seq<ty>, t: tm, T: ty)
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
ghost method monotonic_plus_wfenv(m: nat, n: nat, H: seq<vl>, G: seq<ty>)
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
ghost method monotonic_plus_vtyp(m: nat, n: nat, G: seq<ty>, v: vl, T: ty)
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

// Regularity
ghost method lemma_vtyp_reg(n: nat, G: seq<ty>, v: vl, T: ty) returns (nw: nat)
  requires vtyp(n, G, v, T);
  ensures wf(nw, G, T);
{
  nw := n;
  if (T.TVal? && v.Clos? && vtyp(n, G, v.field, T.Tv)) {
    nw := lemma_vtyp_reg(n, G, v.field, T.Tv);
  }
  else if (n>0 && exists G1, T1 :: sub(n-1, G1, T1, G, T) && vtyp(n-1, G1, v, T1)) {
    var G1, T1 :| sub(n-1, G1, T1, G, T) && vtyp(n-1, G1, v, T1);
    var ns := lemma_sub_rec_reg(n-1, G1, T1, G, T, true);
    nw := ns;
  }
}

ghost method lemma_typ_reg(n: nat, G: seq<ty>, t: tm, T: ty) returns (nw: nat)
  requires typ(n, G, t, T);
  ensures wf(nw, G, T);
{
  nw := n;
  if (t.tnew? &&
      exists TA1, TA2, Tv ::
      typ(n, extend(TA1, G), t.mf, TA2) && typ(n, G, t.field, Tv) &&
      wf(n, G, t.T) &&
      wf(n, G, TArrow(TA1, TA2)) &&
      ((T.TArrow? && T.T1==TA1 && T.T2==TA2) ||
       (T.TVal? && T.Tv==Tv) ||
       (T.TTyp? && T.T==t.T))) {
    var TA1, TA2, Tv :|
      typ(n, extend(TA1, G), t.mf, TA2) && typ(n, G, t.field, Tv) &&
      wf(n, G, t.T) &&
      wf(n, G, TArrow(TA1, TA2)) &&
      ((T.TArrow? && T.T1==TA1 && T.T2==TA2) ||
       (T.TVal? && T.Tv==Tv) ||
       (T.TTyp? && T.T==t.T));
    if (T.TVal? && T.Tv==Tv) {
      var nr := lemma_typ_reg(n, G, t.field, Tv);
      nw := nr;
    }    
  }
  else if (t.tapp? && exists T1 :: typ(n, G, t.a, T1) && typ(n, G, t.f, TArrow(T1, T))) {
    var T1 :| typ(n, G, t.a, T1) && typ(n, G, t.f, TArrow(T1, T));
    var nf := lemma_typ_reg(n, G, t.f, TArrow(T1, T));
    nw := nf;
  }
  else if (t.tget? && typ(n, G, t.o, TVal(T))) {
    var nr := lemma_typ_reg(n, G, t.o, TVal(T));
    nw := nr;
  }
  else if (n>0 && exists T1 :: sub(n-1, G, T1, G, T) && typ(n-1, G, t, T1)) {
    var T1 :| sub(n-1, G, T1, G, T) && typ(n-1, G, t, T1);
    var ns := lemma_sub_rec_reg(n-1, G, T1, G, T, true);
    nw := ns;
  }
}

ghost method lemma_sub_rec_reg(n: nat, G1: seq<ty>, T1: ty, G2: seq<ty>, T2: ty, p: bool) returns (nw: nat)
  requires sub_rec(n, G1, T1, G2, T2, p);
  ensures wf(nw, G1, T1);
  ensures wf(nw, G2, T2);
  decreases n, if (p) then T1 else T2;
{
  if (T1.TInt? && T2.TInt?) {
    nw := 0;
  }
  else if (T2.Top? && wf(n, G1, T1)) {
    nw := n;
  }
  else if (T1.Bot? && wf(n, G2, T2)) {
    nw := n;
  }
  else if (T1.TArrow? && T2.TArrow? && sub_rec(n, G2, T2.T1, G1, T1.T1, !p) && sub_rec(n, G1, T1.T2, G2, T2.T2, p)) {
    var nw1 := lemma_sub_rec_reg(n, G2, T2.T1, G1, T1.T1, !p);
    var nw2 := lemma_sub_rec_reg(n, G1, T1.T2, G2, T2.T2, p);
    nw := nw1+nw2;
    monotonic_plus_wf(nw1, nw, G1, T1.T1);
    monotonic_plus_wf(nw2, nw, G1, T1.T2);
    monotonic_plus_wf(nw1, nw, G2, T2.T1);
    monotonic_plus_wf(nw2, nw, G2, T2.T2);
  }
  else if (T1.TVal? && T2.TVal? && sub_rec(n, G1, T1.Tv, G2, T2.Tv, p)) {
    var nwv := lemma_sub_rec_reg(n, G1, T1.Tv, G2, T2.Tv, p);
    nw := nwv;
  }
  else if (T1.TTyp? && T2.TTyp? && sub_rec(n, G1, T1.T, G2, T2.T, p)) {
    var nwt := lemma_sub_rec_reg(n, G1, T1.T, G2, T2.T, p);
    nw := nwt;
  }
  else if (n>0 && T1.TSel? && exists T1x :: path_eval(n, G1, T1.x, T1x) && sub_rec(n-1, G1, T1x, G2, T2, p)) {
    var T1x :| path_eval(n, G1, T1.x, T1x) && sub_rec(n-1, G1, T1x, G2, T2, p);
    var nwr := lemma_sub_rec_reg(n-1, G1, T1x, G2, T2, p);
    nw := n+nwr+1;
    monotonic_plus_path_eval(n, nw-1, G1, T1.x, T1x);
    monotonic_plus_wf(nwr, nw, G2, T2);
  }
  else if (n>0 && T2.TSel? && exists T2x :: path_eval(n, G2, T2.x, T2x) && sub_rec(n-1, G1, T1, G2, T2x, p)) {
    var T2x :| path_eval(n, G2, T2.x, T2x) && sub_rec(n-1, G1, T1, G2, T2x, p);
    var nwr := lemma_sub_rec_reg(n-1, G1, T1, G2, T2x, p);
    nw := n+nwr+1;
    monotonic_plus_path_eval(n, nw-1, G2, T2.x, T2x);
    monotonic_plus_wf(nwr, nw, G1, T1);
  }
}

// Reflexivity
ghost method lemma_sub_rec_refl(n: nat, G: seq<ty>, T: ty, p: bool) returns (ns: nat)
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

// Transitivity
ghost method {:timeLimit 80} lemma_sub_rec_trans(n12: nat, n23: nat, G1: seq<ty>, T1: ty, G2: seq<ty>, T2: ty, G3: seq<ty>, T3: ty, p: bool) returns (n13: nat)
  requires sub_rec(n12, G1, T1, G2, T2, p);
  requires sub_rec(n23, G2, T2, G3, T3, p);
  ensures sub_rec(n13, G1, T1, G3, T3, p);
  decreases if p then n12 else n23, if p then n23 else n12, if p then T1 else T3, T2, if p then T3 else T1;
{
  n13 := 0;
  if (T3.Top? && wf(n23, G2, T2)) {
    var nw1 := lemma_sub_rec_reg(n12, G1, T1, G2, T2, p);
    n13 := nw1;
  }
  else if (T1.Bot? && wf(n12, G2, T2)) {
    var nw3 := lemma_sub_rec_reg(n23, G2, T2, G3, T3, p);
    n13 := nw3;
  }
  else if (T1.TArrow? && T2.TArrow? && T3.TArrow?) {
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

/// Context weakening
ghost method wkn_path_eval(Tz: ty, n: nat, G: seq<ty>, x: nat, T: ty)
  requires path_eval(n, G, x, T);
  ensures path_eval(n, extend(Tz, G), x, T);
{
  assert n>0 && lookup(x, G).Result? && lookup(x, G).get==T && wf(n-1, G, T);
  assert lookup(x, extend(Tz, G)).Result?;
  wkn_wf(Tz, n-1, G, T);
}
ghost method wkn_wf(Tz: ty, n: nat, G: seq<ty>, T: ty)
  requires wf(n, G, T);
  ensures wf(n, extend(Tz, G), T);
{
  if (n>0 && T.TSel? && exists Tx :: path_eval(n-1, G, T.x, Tx)) {
    var Tx :| path_eval(n-1, G, T.x, Tx);
    wkn_path_eval(Tz, n-1, G, T.x, Tx);
  }
}
ghost method wkn_sub(Tz: ty, n: nat, G1: seq<ty>, T1: ty, G2: seq<ty>, T2: ty)
  requires sub(n, G1, T1, G2, T2);
  ensures sub(n, extend(Tz, G1), T1, extend(Tz, G2), T2);
  ensures sub(n, extend(Tz, G1), T1, G2, T2);
  ensures sub(n, G1, T1, extend(Tz, G2), T2);
{
  wkn_sub_rec(Tz, n, G1, T1, G2, T2, true);
}
ghost method wkn_sub_rec(Tz: ty, n: nat, G1: seq<ty>, T1: ty, G2: seq<ty>, T2: ty, p: bool)
  requires sub_rec(n, G1, T1, G2, T2, p);
  ensures sub_rec(n, extend(Tz, G1), T1, extend(Tz, G2), T2, p);
  ensures sub_rec(n, extend(Tz, G1), T1, G2, T2, p);
  ensures sub_rec(n, G1, T1, extend(Tz, G2), T2, p);
  decreases n, if (p) then T1 else T2;
{ 
  if (T2.Top? && wf(n, G1, T1)) {
    wkn_wf(Tz, n, G1, T1);
  }
  else if (T1.Bot? && wf(n, G2, T2)) {
    wkn_wf(Tz, n, G2, T2);
  }
  else if (n>0 && T1.TSel? && exists T1x :: path_eval(n, G1, T1.x, T1x) && sub_rec(n-1, G1, T1x, G2, T2, p)) {
    var T1x :| path_eval(n, G1, T1.x, T1x);
    wkn_path_eval(Tz, n, G1, T1.x, T1x);
    wkn_sub_rec(Tz, n-1, G1, T1x, G2, T2, p);
  }
  else if (T2.TSel? && exists T2x :: path_eval(n, G2, T2.x, T2x) && sub_rec(n-1, G1, T1, G2, T2x, p)) {
    var T2x :| path_eval(n, G2, T2.x, T2x);
    wkn_path_eval(Tz, n, G2, T2.x, T2x);
    wkn_sub_rec(Tz, n-1, G1, T1, G2, T2x, p);
  }
}
ghost method wkn_vtyp(Tz: ty, n: nat, G: seq<ty>, v: vl, T: ty)
  requires vtyp(n, G, v, T);
  ensures vtyp(n, extend(Tz, G), v, T);
{
  if (T.TArrow? && v.Clos? && wf(n, G, T) && exists Gc :: wfenv(n, v.H, Gc) && typ(n, extend(T.T1, Gc), v.mf, T.T2) && sub(n, Gc, T, G, T)) {
    wkn_wf(Tz, n, G, T);
    var Gc :| wfenv(n, v.H, Gc) && typ(n, extend(T.T1, Gc), v.mf, T.T2) && sub(n, Gc, T, G, T);
    wkn_sub(Tz, n, Gc, T, G, T);
  }
  else if (T.TTyp? && v.Clos? && wf(n, G, T.T)) {
    wkn_wf(Tz, n, G, T.T);
  }
  else if (n>0 && exists G1, T1 :: sub(n-1, G1, T1, G, T) && vtyp(n-1, G1, v, T1)) {
    var G1, T1 :| sub(n-1, G1, T1, G, T) && vtyp(n-1, G1, v, T1);
    wkn_sub(Tz, n-1, G1, T1, G, T);
    wkn_vtyp(Tz, n-1, G1, v, T1);
    wkn_sub(Tz, n-1, G1, T1, G, T);
    help_vtyp_sub(n, extend(Tz, G), v, T, extend(Tz, G1), T1);
  }
}
ghost method wkn_plus_vtyp(Ts: seq<ty>, n: nat, G: seq<ty>, v: vl, T: ty)
  requires vtyp(n, G, v, T);
  ensures vtyp(n, G+Ts, v, T);
{
  if (Ts==[]) {
    assert G+Ts==G;
  }
  else {
    wkn_vtyp(Ts[0], n, G, v, T);
    wkn_plus_vtyp(Ts[1..], n, extend(Ts[0], G), v, T);
    assert extend(Ts[0], G)+Ts[1..]==G+Ts;
  }
}

// Inversions

ghost method inv_typ_var(n: nat, G: seq<ty>, x: nat, T: ty) returns (ni: nat)
  requires typ(n, G, tvar(x), T);
  ensures lookup(x, G).Result?;
  ensures sub(ni, G, lookup(x, G).get, G, T);
{
  if (lookup(x, G)==Result(T) && wf(n, G, T)) {
    var nr := lemma_sub_rec_refl(n, G, T, true);
    ni := nr;
  }
  else if (n>0 && exists T' :: sub(n-1, G, T', G, T) && typ(n-1, G, tvar(x), T')) {
    var T' :| sub(n-1, G, T', G, T) && typ(n-1, G, tvar(x), T');
    var nr := inv_typ_var(n-1, G, x, T');
    var ns := lemma_sub_rec_trans(nr, n-1, G, lookup(x, G).get, G, T', G, T, true);
    ni := ns;
  }
}

ghost method inv_typ_num(n: nat, G: seq<ty>, i: int, T: ty) returns (ni: nat)
  requires typ(n, G, tnum(i), T);
  ensures typ(ni, G, tnum(i), TInt);
  ensures sub(ni, G, TInt, G, T);
{
  ni := 0;
  if (n>0 && exists T' :: sub(n-1, G, T', G, T) && typ(n-1, G, tnum(i), T')) {
    var T' :| sub(n-1, G, T', G, T) && typ(n-1, G, tnum(i), T');
    var nr := inv_typ_num(n-1, G, i, T');
    var ns := lemma_sub_rec_trans(nr, n-1, G, TInt, G, T', G, T, true);
    ni := ns;
  }
}

ghost method help_sub_cases(n: nat, G: seq<ty>, Tm1: ty, Tm2: ty, Tf: ty, Tx: ty, T: ty)
  requires (T.TArrow? && T.T1==Tm1 && T.T2==Tm2)
        || (T.TVal? && T.Tv==Tf)
        || (T.TTyp? && T.T==Tx);
  requires sub(n, G, T, G, T);
  ensures sub(n, G, TArrow(Tm1, Tm2), G, T)
       || sub(n, G, TVal(Tf), G, T)
       || sub(n, G, TTyp(Tx), G, T);
{
}

ghost method inv_typ_new(n: nat, G: seq<ty>, mf: tm, ff: tm, Tx: ty, T: ty) returns (ni: nat, Tm1: ty, Tm2: ty, Tf: ty)
  requires typ(n, G, tnew(mf, ff, Tx), T);
  ensures typ(ni, extend(Tm1, G), mf, Tm2);
  ensures typ(ni, G, ff, Tf);
  ensures wf(ni, G, TArrow(Tm1, Tm2));
  ensures wf(ni, G, Tx);
  ensures sub(ni, G, TArrow(Tm1, Tm2), G, T)
       || sub(ni, G, TVal(Tf), G, T)
       || sub(ni, G, TTyp(Tx), G, T);
{
  if (exists TA1, TA2, Tv ::
      typ(n, extend(TA1, G), mf, TA2) && typ(n, G, ff, Tv) &&
      wf(n, G, Tx) &&
      wf(n, G, TArrow(TA1, TA2)) &&
      ((T.TArrow? && T.T1==TA1 && T.T2==TA2) ||
       (T.TVal? && T.Tv==Tv) ||
       (T.TTyp? && T.T==Tx))) {
    var TA1, TA2, Tv :|
        typ(n, extend(TA1, G), mf, TA2) && typ(n, G, ff, Tv) &&
        wf(n, G, Tx) &&
        wf(n, G, TArrow(TA1, TA2)) &&
        ((T.TArrow? && T.T1==TA1 && T.T2==TA2) ||
         (T.TVal? && T.Tv==Tv) ||
         (T.TTyp? && T.T==Tx));
    Tm1 := TA1;
    Tm2 := TA2;
    Tf := Tv;
    var nw := lemma_typ_reg(n, G, tnew(mf, ff, Tx), T);
    var ns := lemma_sub_rec_refl(nw, G, T, true);
    ni := ns+n;
    monotonic_plus_sub(ns, ni, G, T, G, T);
    monotonic_plus_typ(n, ni, extend(Tm1, G), mf, Tm2);
    monotonic_plus_typ(n, ni, G, ff, Tf);
    monotonic_plus_wf(n, ni, G, TArrow(Tm1, Tm2));
    monotonic_plus_wf(n, ni, G, Tx);
    help_sub_cases(ni, G, Tm1, Tm2, Tf, Tx, T);
  }
  else if (n>0 && exists T1 :: sub(n-1, G, T1, G, T) && typ(n-1, G, tnew(mf, ff, Tx), T1)) {
    var T1 :| sub(n-1, G, T1, G, T) && typ(n-1, G, tnew(mf, ff, Tx), T1);
    var ni', Tm1', Tm2', Tf' := inv_typ_new(n-1, G, mf, ff, Tx, T1);
    Tm1 := Tm1';
    Tm2 := Tm2';
    Tf := Tf';
    var Ts := T;
    if (sub(ni', G, TArrow(Tm1, Tm2), G, T1)) {
      Ts := TArrow(Tm1, Tm2);  
    }
    else if (sub(ni', G, TVal(Tf), G, T1)) {
      Ts := TVal(Tf);
    }
    else if (sub(ni', G, TTyp(Tx), G, T1)) {
      Ts := TTyp(Tx);
    }
    else {
      assert false;
    }
    var ns := lemma_sub_rec_trans(ni', n-1, G, Ts, G, T1, G, T, true);
    ni := ni'+ns;
    monotonic_plus_typ(ni', ni, extend(Tm1, G), mf, Tm2);
    monotonic_plus_typ(ni', ni, G, ff, Tf);
    monotonic_plus_wf(ni', ni, G, TArrow(Tm1, Tm2));
    monotonic_plus_wf(ni', ni, G, Tx);
    monotonic_plus_sub(ns, ni, G, Ts, G, T);
  }
}

ghost method inv_typ_get(n: nat, G: seq<ty>, o: tm, T: ty) returns (ni: nat, T1: ty)
  requires typ(n, G, tget(o), T);
  ensures typ(ni, G, o, TVal(T1));
  ensures sub(ni, G, T1, G, T);
{
  if (typ(n, G, o, TVal(T))) {
    T1 := T;
    var nw := lemma_typ_reg(n, G, o, TVal(T));
    var ns := lemma_sub_rec_refl(nw, G, T, true);
    ni := n+ns;
    monotonic_plus_typ(n, ni, G, o, TVal(T));
    monotonic_plus_sub(ns, ni, G, T, G, T);
  }
  else if (n>0 && exists T1 :: sub(n-1, G, T1, G, T) && typ(n-1, G, tget(o), T1)) {
    var T' :| sub(n-1, G, T', G, T) && typ(n-1, G, tget(o), T');
    var nr, T1' := inv_typ_get(n-1, G, o, T');
    T1 := T1';
    var ns := lemma_sub_rec_trans(nr, n-1, G, T1, G, T', G, T, true);
    ni := nr+ns;
    monotonic_plus_typ(nr, ni, G, o, TVal(T1));
    monotonic_plus_sub(ns, ni, G, T1, G, T);
  }
}

ghost method inv_vtyp_val_aux(n: nat, nsub: nat, G: seq<ty>, G1': seq<ty>, v: vl, T: ty, T1': ty) returns (ni: nat, G1: seq<ty>, T1: ty)
  requires vtyp(n, G, v, T);
  requires sub(nsub, G, T, G1', TVal(T1'));
  ensures v.Clos?;
  ensures vtyp(ni, G1, v.field, T1);
  ensures sub(ni, G1, TVal(T1), G1', TVal(T1'));
{
  if (T.TVal? && v.Clos? && vtyp(n, G, v.field, T.Tv)) {
    T1 := T.Tv;
    G1 := G;
    var nw := lemma_vtyp_reg(n, G, v, T);
    var nr := lemma_sub_rec_refl(nw, G, T, true);
    var ns := lemma_sub_rec_trans(nr, nsub, G, T, G, T, G1', TVal(T1'), true);
    ni := n+ns;
    monotonic_plus_vtyp(n, ni, G1, v.field, T1);
    monotonic_plus_sub(ns, ni, G1, TVal(T1), G1', TVal(T1'));
  } else if (n>0 && exists G', T' :: sub(n-1, G', T', G, T) && vtyp(n-1, G', v, T')) {
    var G', T' :| sub(n-1, G', T', G, T) && vtyp(n-1, G', v, T');
    var ns := lemma_sub_rec_trans(n-1, nsub, G', T', G, T, G1', TVal(T1'), true);
    var ni_, G1_, T1_ := inv_vtyp_val_aux(n-1, ns, G', G1', v, T', T1');
    G1 := G1_;
    T1 := T1_;
    ni := ni_;
  }
}

ghost method inv_vtyp_val(n: nat, G: seq<ty>, v: vl, T: ty) returns (ni: nat, G1: seq<ty>, T1: ty)
  requires vtyp(n, G, v, TVal(T));
  ensures v.Clos?;
  ensures vtyp(ni, G1, v.field, T1);
  ensures sub(ni, G1, TVal(T1), G, TVal(T));
{
  var nw := lemma_vtyp_reg(n, G, v, TVal(T));
  var ns := lemma_sub_rec_refl(nw, G, T, true);
  ni, G1, T1 := inv_vtyp_val_aux(n, ns, G, G, v, TVal(T), T);
}

ghost method inv_typ_app(n: nat, G: seq<ty>, f: tm, a: tm, T: ty) returns (ni: nat, T1: ty, T2: ty)
  requires typ(n, G, tapp(f, a), T);
  ensures typ(ni, G, f, TArrow(T1, T2));
  ensures typ(ni, G, a, T1);
  ensures sub(ni, G, T2, G, T);
{
  if (exists T1' :: typ(n, G, a, T1') && typ(n, G, f, TArrow(T1', T))) {
    var T1' :| typ(n, G, a, T1') && typ(n, G, f, TArrow(T1', T));
    T1 := T1';
    T2 := T;
    var nw := lemma_typ_reg(n, G, tapp(f, a), T);
    var ns := lemma_sub_rec_refl(nw, G, T, true);
    ni := n+ns;
    monotonic_plus_typ(n, ni, G, f, TArrow(T1, T2));
    monotonic_plus_typ(n, ni, G, a, T1);
    monotonic_plus_sub(ns, ni, G, T2, G, T);
  }
  else if (n>0 && exists T' :: sub(n-1, G, T', G, T) && typ(n-1, G, tapp(f, a), T')) {
    var T' :| sub(n-1, G, T', G, T) && typ(n-1, G, tapp(f, a), T');
    var nr, T1', T2' := inv_typ_app(n-1, G, f, a, T');
    T1 := T1';
    T2 := T2';
    var ns := lemma_sub_rec_trans(nr, n-1, G, T2, G, T', G, T, true);
    ni := nr+ns;
    monotonic_plus_typ(nr, ni, G, f, TArrow(T1, T2));
    monotonic_plus_typ(nr, ni, G, a, T1);
    monotonic_plus_sub(ns, ni, G, T2, G, T);
  }
}

ghost method inv_vtyp_fun_aux(n: nat, nsub: nat, G: seq<ty>, G': seq<ty>, v: vl, T: ty, T1': ty, T2': ty) returns (ni: nat, Gr: seq<ty>, T1: ty, T2: ty)
  requires vtyp(n, G, v, T);
  requires sub(nsub, G, T, G', TArrow(T1', T2')); 
  ensures v.Clos?;
  ensures typ(ni, extend(T1, Gr), v.mf, T2);
  ensures wfenv(ni, v.H, Gr);
  ensures sub(ni, Gr, TArrow(T1, T2), G', TArrow(T1', T2'));
{
  if (T.TArrow? && v.Clos? && wf(n, G, T) && exists Gc :: wfenv(n, v.H, Gc) && typ(n, extend(T.T1, Gc), v.mf, T.T2) && sub(n, Gc, T, G, T)) {
    var Gc :| wfenv(n, v.H, Gc) && typ(n, extend(T.T1, Gc), v.mf, T.T2) && sub(n, Gc, T, G, T);
    T1 := T.T1;
    T2 := T.T2;
    Gr := Gc;
    var ns := lemma_sub_rec_trans(n, nsub, Gr, T, G, T, G', TArrow(T1', T2'), true);
    ni := ns+n;
    monotonic_plus_typ(n, ni, extend(T1, Gr), v.mf, T2);
    monotonic_plus_wfenv(n, ni, v.H, Gr);
    monotonic_plus_sub(ns, ni, Gr, TArrow(T1, T2), G', TArrow(T1', T2'));
  }
  else if (n>0 && exists G_, T_ :: sub(n-1, G_, T_, G, T) && vtyp(n-1, G_, v, T_)) {
    var G_, T_ :| sub(n-1, G_, T_, G, T) && vtyp(n-1, G_, v, T_);
    var ns := lemma_sub_rec_trans(n-1, nsub, G_, T_, G, T, G', TArrow(T1', T2'), true);
    var nir, Grr, T1r, T2r := inv_vtyp_fun_aux(n-1, ns, G_, G', v, T_, T1', T2');
    ni := nir;
    Gr := Grr;
    T1 := T1r;
    T2 := T2r;
  }
}

ghost method inv_vtyp_fun(n: nat, G': seq<ty>, v: vl, T1': ty, T2': ty) returns (ni: nat, G: seq<ty>, T1: ty, T2: ty)
  requires vtyp(n, G', v, TArrow(T1', T2'));
  ensures v.Clos?;
  ensures typ(ni, extend(T1, G), v.mf, T2);
  ensures wfenv(ni, v.H, G);
  ensures sub(ni, G, TArrow(T1, T2), G', TArrow(T1', T2'));
{
  var nw := lemma_vtyp_reg(n, G', v, TArrow(T1', T2'));
  var ns := lemma_sub_rec_refl(nw, G', TArrow(T1', T2'), true);
  ni, G, T1, T2 := inv_vtyp_fun_aux(n, ns, G', G', v, TArrow(T1', T2'), T1', T2');
}

// Safety properties
ghost method theorem_lookup_safe(nw: nat, H: seq<vl>, G: seq<ty>, x: nat)
  requires wfenv(nw, H, G);
  requires lookup(x, G).Result?;
  ensures lookup(x, H).Result?;
  ensures vtyp(nw, G[..x], lookup(x, H).get, lookup(x, G).get);
  ensures vtyp(nw, G, lookup(x, H).get, lookup(x, G).get);
{
  assert lookup(x, G).get==G[x];
  assert |H|==|G|;
  assert lookup(x, H).get==H[x];
  wkn_plus_vtyp(G[x..], nw, G[..x], lookup(x, H).get, lookup(x, G).get);
  assert G[..x]+G[x..]==G;
}

ghost method help_wfenv_extend(nif: nat, na: nat, Hf: seq<vl>, Gf: seq<ty>, T1f: ty, G: seq<ty>, T1: ty, va: vl) returns (nw: nat)
  requires sub(nif, G, T1, Gf, T1f);
  requires vtyp(na, G, va, T1);
  requires wfenv(nif, Hf, Gf);
  ensures wfenv(nw, extend(va, Hf), extend(T1f, Gf));
{
  var naf := nif+na+1;
  monotonic_plus_sub(nif, naf-1, G, T1, Gf, T1f);
  monotonic_plus_vtyp(na, naf-1, G, va, T1);
  help_vtyp_sub(naf, Gf, va, T1f, G, T1);
  nw := naf;
  monotonic_plus_wfenv(nif, nw, Hf, Gf);
  help_wfenv_extend_simple(nw, Hf, Gf, va, T1f);
}

ghost method help_wfenv_extend_simple(n: nat, H: seq<vl>, G: seq<ty>, v: vl, T: ty) 
  requires wfenv(n, H, G);
  requires vtyp(n, G, v, T);
  ensures wfenv(n, extend(v, H), extend(T, G));
{
  assert |extend(v, H)|==|H|+1;
  assert |extend(T, G)|==|G|+1;
  assert |H|==|G|;
  forall (x | 0 <= x < |extend(v, H)|)
  ensures vtyp(n, extend(T, G)[..x], extend(v, H)[x], extend(T, G)[x]);
  {
    assert extend(T, G)[..x]==G[..x];
    if (x == |extend(v, H)|-1) {
      assert extend(v, H)[x]==v;
      assert extend(T, G)[x]==T;
    }
  }
}

ghost method {:timeLimit 50} theorem_eval_safe(nw: nat, H: seq<vl>, G: seq<ty>, nt: nat, t: tm, T: ty, ne: nat) returns (nv: nat)
  requires wfenv(nw, H, G);
  requires typ(nt, G, t, T);
  ensures !eval(ne, H, t).Stuck?;
  ensures eval(ne, H, t).Result? ==> vtyp(nv, G, eval(ne, H, t).get, T);
  decreases ne, t;
{
  match t {
  case tnum(n) =>
    var ni := inv_typ_num(nt, G, n, T);
    nv := ni+1;
  case tvar(x) =>
    var ni := inv_typ_var(nt, G, x, T);
    theorem_lookup_safe(nw, H, G, x);
    nv := nw+ni;
    monotonic_plus_vtyp(nw, nv, G, lookup(x, H).get, lookup(x, G).get);
    monotonic_plus_sub(ni, nv, G, lookup(x, G).get, G, T);
    nv := nv+1;
    help_vtyp_sub(nv, G, eval(ne, H, t).get, T, G, lookup(x, G).get);
  case tnew(mf, ff, Tx) =>
    var ni, Tm1, Tm2, Tf := inv_typ_new(nt, G, mf, ff, Tx, T);
    var nr := theorem_eval_safe(nw, H, G, ni, ff, Tf, ne);
    var vff := eval(ne, H, ff);
    var vo := eval(ne, H, t);
    assert !vff.Stuck?;
    assert !vo.Stuck?;
    if (vff.Result?) {
      assert vo.Result?;
      var v := vo.get; 
      var T1 := T;
      if sub(ni, G, TArrow(Tm1, Tm2), G, T) {
        T1 := TArrow(Tm1, Tm2);
        assert wf(ni, G, TArrow(Tm1, Tm2));
        assert wfenv(nw, v.H, G);
        assert typ(ni, extend(Tm1, G), v.mf, Tm2);
        var nr := lemma_sub_rec_refl(ni, G, TArrow(Tm1, Tm2), true);
        assert sub(nr, G, TArrow(Tm1, Tm2), G, TArrow(Tm1, Tm2));
        nv := ni+nw+nr;
        monotonic_plus_wf(ni, nv, G, TArrow(Tm1, Tm2));
        monotonic_plus_wfenv(nw, nv, v.H, G);
        monotonic_plus_typ(ni, nv, extend(Tm1, G), v.mf, Tm2);
        monotonic_plus_sub(nr, nv, G, TArrow(Tm1, Tm2), G, TArrow(Tm1, Tm2));
        monotonic_plus_sub(ni, nv, G, TArrow(Tm1, Tm2), G, T);
        nv := nv+1;
      }
      else if sub(ni, G, TVal(Tf), G, T) {
        T1 := TVal(Tf);
        nv := ni+nr;
        monotonic_plus_vtyp(nr, nv, G, v, TVal(Tf));
        monotonic_plus_sub(ni, nv, G, TVal(Tf), G, T);
        nv := nv+1;
      }
      else if sub(ni, G, TTyp(Tx), G, T) {
        T1 := TTyp(Tx);
        nv := ni+1;
      }
      else {
        assert false;
      }
      help_vtyp_sub(nv, G, eval(ne, H, t).get, T, G, T1);
    }
  case tapp(f, a) =>
    var ni, T1, T2 := inv_typ_app(nt, G, f, a, T);
    var nf := theorem_eval_safe(nw, H, G, ni, f, TArrow(T1, T2), ne);
    var na := theorem_eval_safe(nw, H, G, ni, a, T1, ne);
    var vfo := eval(ne, H, f);
    var vao := eval(ne, H, a);
    var vo := eval(ne, H, t);
    assert !vfo.Stuck? && !vao.Stuck?;
    if (vfo.Result? && vao.Result?) {
      if (ne==0) {
      } else {
        var vf := vfo.get;
        var va := vao.get;
        var nif, Gf, T1f, T2f := inv_vtyp_fun(nf, G, vf, T1, T2);
        invariant_p_sub_rec(nif, G, T1, Gf, T1f, false);
        var nwef := help_wfenv_extend(nif, na, vf.H, Gf, T1f, G, T1, va);
        var nr := theorem_eval_safe(nwef, extend(va, vf.H), extend(T1f, Gf), nif, vf.mf, T2f, ne-1);
        assert vo==eval(ne-1, extend(va, vf.H), vf.mf);
        assert !vo.Stuck?;
        if (vo.Result?) {
          var v := vo.get;
          assert vtyp(nr, extend(T1f, Gf), v, T2f);
          var ns := lemma_sub_rec_trans(nif, ni, Gf, T2f, G, T2, G, T, true);
          wkn_sub(T1f, ns, Gf, T2f, G, T);
          nv := nr + ns;
          monotonic_plus_vtyp(nr, nv, extend(T1f, Gf), v, T2f);
          monotonic_plus_sub(ns, nv, extend(T1f, Gf), T2f, G, T);
          help_vtyp_sub(nv+1, G, eval(ne, H, t).get, T, extend(T1f, Gf), T2f);
          nv := nv+1;
        }
      }
    }
  case tget(o) =>
    var ni, T1 := inv_typ_get(nt, G, o, T);
    var nr := theorem_eval_safe(nw, H, G, ni, o, TVal(T1), ne);
    if (eval(ne, H, o).Result?) {
      var niv, G1v, T1v := inv_vtyp_val(nr, G, eval(ne, H, o).get, T1);
      assert vtyp(niv, G1v, eval(ne, H, t).get, T1v);
      assert sub(niv, G1v, TVal(T1v), G, TVal(T1));
      help_vtyp_sub(niv+1, G, eval(ne, H, t).get, T1, G1v, T1v);
      nv := niv+1+ni;
      monotonic_plus_vtyp(niv+1, nv, G, eval(ne, H, t).get, T1);
      monotonic_plus_sub(ni, nv, G, T1, G, T);
      help_vtyp_sub(nv+1, G, eval(ne, H, t).get, T, G, T1);
      nv := nv+1;
    }
  }
}
