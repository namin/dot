// ============================
// Dependent Object Types (DOT)
// ============================

// ---------
// Utilities
// ---------

// ### List ###
datatype list<A> = Nil | Cons(head: A, tail: list<A>);

// ### Pair ###
datatype pair<A, B> = P(fst: A, snd: B);

// ### Option ###
datatype option<A> = None | Some(get: A);

function seq2lst<A>(s: seq<A>): list<A>
{
  if (s == []) then Nil
  else Cons(s[0], seq2lst(s[1..]))
}
function lst2seq<A>(lst: list<A>): seq<A>
{
  match lst
  case Nil => []
  case Cons(head, tail) => [head] + lst2seq(tail)
}
function max(s: seq<int>, start: int): int
  ensures max(s, start)>=start;
  ensures forall x :: x in s ==> x<=max(s, start);
{
  if (s == []) then start
  else if (s[0] <= start) then max(s[1..], start)
  else max(s[1..], s[0])
}
function fresh_from(ids: seq<int>): int
  ensures fresh_from(ids) !in ids;
  ensures fresh_from(ids)>=0;
{
  max(ids, -1)+1
}

// ------
// Syntax
// ------

datatype tp = tp_sel(p: tm, L: nat, concrete: bool) | tp_rfn(base_tp: tp, self: nat, decls: list<decl>) | tp_and(and1: tp, and2: tp) | tp_or(or1: tp, or2: tp) | tp_top | tp_bot;
datatype tm = tm_var(x: nat) | tm_new(y: nat, Tc: tp, init: list<def>, t': tm) | tm_sel(t: tm, l: nat) | tm_msel(o: tm, m: nat, a: tm) | tm_loc(loc: nat);
datatype decl = decl_tp(L: nat, S: tp, U: tp, concrete: bool) | decl_tm(l: nat, T: tp) | decl_mt(m: nat, P: tp, R: tp);
datatype def = def_tm(l: nat, t: tm) | def_mt(m: nat, param: nat, body: tm);
datatype decls = decls_fin(decls: list<decl>) | decls_bot;

predicate path(t: tm)
{
  t.tm_loc? || t.tm_var? || (t.tm_sel? && path(t.t))
}

predicate is_concrete(T: tp)
{
  (T.tp_sel? && T.concrete && path(T.p)) ||
  (T.tp_rfn? && is_concrete(T.base_tp)) ||
  (T.tp_and? && is_concrete(T.and1) && is_concrete(T.and2)) ||
  T.tp_top?
}

function decl_label(d: decl): nat
{
  match d
  case decl_tp(L, S, U, concrete) => L
  case decl_tm(l, T) => l
  case decl_mt(m, P, R) => m
}

// ---------------------
// Operational Semantics
// ---------------------

// ### Values ###
predicate value(t: tm)
{
  t.tm_loc?
}
predicate syn_value(t: tm)
{
  t.tm_loc? || t.tm_var?
}

// ### Store ###
datatype store = Store(m: seq<pair<tp, seq<def>>>);
function store_lookup(loc: nat, s: store): seq<def>
  requires loc < |s.m|;
{
  s.m[loc].snd
}
function store_lookup_type(loc: nat, s: store): tp
  requires loc < |s.m|;
{
  s.m[loc].fst
}
function def_method_lookup(m: nat, defs: seq<def>): option<pair<int, tm>>
  ensures def_method_lookup(m, defs).Some? ==> def_method_lookup(m, defs).get.fst>=0;
{
  if (exists i :: 0 <= i < |defs| && defs[i].def_mt? && defs[i].m==m)
  then (var i :| 0 <= i < |defs| && defs[i].def_mt? && defs[i].m==m; Some(P(defs[i].param, defs[i].body)))
  else None
}
function def_field_lookup(l: nat, defs: seq<def>): option<tm>
{
  if (exists i :: 0 <= i < |defs| && defs[i].def_tm? && defs[i].l==l)
  then (var i :| 0 <= i < |defs| && defs[i].def_tm? && defs[i].l==l; Some(defs[i].t))
  else None
}

// ### Size ###
function tm_size(t: tm): nat
  ensures t.tm_new? ==> tm_size(t)==1+tp_size(t.Tc)+defs_size(t.init)+tm_size(t.t');
  ensures t.tm_new? ==> tm_size(t)>tp_size(t.Tc);
  ensures t.tm_new? ==> tm_size(t)>defs_size(t.init);
  ensures t.tm_new? ==> tm_size(t)>tm_size(t.t');
  ensures t.tm_sel? ==> tm_size(t)==1+tm_size(t.t);
  ensures t.tm_msel? ==> tm_size(t)==1+tm_size(t.o)+tm_size(t.a);
  ensures t.tm_msel? ==> tm_size(t)>tm_size(t.o);
{
  match t
  case tm_var(x') => 1
  case tm_new(y, Tc, init, t1) => 1+tp_size(Tc)+defs_size(init)+tm_size(t1)
  case tm_sel(t1, l) => 1+tm_size(t1)
  case tm_msel(o, m, a) => 1+tm_size(o)+tm_size(a)
  case tm_loc(loc) => 1
}
function tp_size(T: tp): nat
  ensures T.tp_sel? ==> tp_size(T)==1+tm_size(T.p);
  ensures T.tp_sel? ==> tp_size(T)>tm_size(T.p);
  ensures T.tp_rfn? ==> tp_size(T)==1+tp_size(T.base_tp)+decls_size(T.decls);
  ensures T.tp_rfn? ==> tp_size(T)>tp_size(T.base_tp);
  ensures T.tp_rfn? ==> tp_size(T)>decls_size(T.decls);
  ensures T.tp_and? ==> tp_size(T)==1+tp_size(T.and1)+tp_size(T.and2);
  ensures T.tp_and? ==> tp_size(T)>tp_size(T.and1);
  ensures T.tp_or? ==> tp_size(T)==1+tp_size(T.or1)+tp_size(T.or2);
  ensures T.tp_or? ==> tp_size(T)>tp_size(T.or1);
{
  match T
  case tp_sel(p, L, concrete) => 1+tm_size(p)
  case tp_rfn(base_tp, self, decls) => 1+tp_size(base_tp)+decls_size(decls)
  case tp_and(and1, and2) => 1+tp_size(and1)+tp_size(and2)
  case tp_or(or1, or2) => 1+tp_size(or1)+tp_size(or2)
  case tp_top => 1
  case tp_bot => 1
}
function def_size(d: def): nat
  ensures d.def_tm? ==> def_size(d)==1+tm_size(d.t);
  ensures d.def_tm? ==> def_size(d)>tm_size(d.t);
  ensures d.def_mt? ==> def_size(d)==1+tm_size(d.body);
  ensures d.def_mt? ==> def_size(d)>tm_size(d.body);
{
  match d
  case def_tm(l, t1) => 1+tm_size(t1)
  case def_mt(m, param, body) => 1+tm_size(body)
}
function decl_size(d: decl): nat
  ensures d.decl_tp? ==> decl_size(d)==1+tp_size(d.S)+tp_size(d.U);
  ensures d.decl_tp? ==> decl_size(d)>tp_size(d.S);
  ensures d.decl_tp? ==> decl_size(d)>tp_size(d.U);
  ensures d.decl_tm? ==> decl_size(d)==1+tp_size(d.T);
  ensures d.decl_tm? ==> decl_size(d)>tp_size(d.T);
  ensures d.decl_mt? ==> decl_size(d)==1+tp_size(d.P)+tp_size(d.R);
  ensures d.decl_mt? ==> decl_size(d)>tp_size(d.P);
  ensures d.decl_mt? ==> decl_size(d)>tp_size(d.R);
{
  match d
  case decl_tp(L, S, U, concrete) => 1+tp_size(S)+tp_size(U)
  case decl_tm(l, T) => 1+tp_size(T)
  case decl_mt(m, P, R) => 1+tp_size(P)+tp_size(R)
}
function defs_size(defs: list<def>): nat
  ensures defs.Cons? ==> defs_size(defs)==1+def_size(defs.head)+defs_size(defs.tail);
  ensures defs.Cons? ==> defs_size(defs)>def_size(defs.head);
{
  match defs
  case Nil => 1
  case Cons(head, tail) => 1+def_size(head)+defs_size(tail)
}
function decls_size(decls: list<decl>): nat
  ensures decls.Cons? ==> decls_size(decls)==1+decl_size(decls.head)+decls_size(decls.tail);
  ensures decls.Cons? ==> decls_size(decls)>decl_size(decls.head);
{
  match decls
  case Nil => 1
  case Cons(head, tail) => 1+decl_size(head)+decls_size(tail)
}

// ### Substitution ###
function tm_subst(x: nat, v: tm, t: tm): tm
  decreases tm_size(t), t;
  ensures v.tm_var? ==> tm_size(t)==tm_size(tm_subst(x, v, t));
{
  match t
  case tm_var(x') => if x'==x then v else t
  case tm_new(y, Tc, init, t1) =>
    if y==x then tm_new(y, tp_subst(x, v, Tc), init, t1) else
    var y' := if (tm_fn(y, v)) then fresh_from([x]+tm_vars(v)+tm_vars(t)) else y;
    var init' := if (y==y') then init else defs_subst(y, tm_var(y'), init);
    var t1' := if (y==y') then t1 else tm_subst(y, tm_var(y'), t1);
    tm_new(y', tp_subst(x, v, Tc), defs_subst(x, v, init'), tm_subst(x, v, t1'))
  case tm_sel(t1, l) => tm_sel(tm_subst(x, v, t1), l)
  case tm_msel(o, m, a) => tm_msel(tm_subst(x, v, o), m, tm_subst(x, v, a))
  case tm_loc(loc) => t
}
function tp_subst(x: nat, v: tm, T: tp): tp
  decreases tp_size(T), T;
  ensures v.tm_var? ==> tp_size(T)==tp_size(tp_subst(x, v, T));
{
  match T
  case tp_sel(p, L, concrete) => tp_sel(tm_subst(x, v, p), L, concrete)
  case tp_rfn(base_tp, self, decls) =>
    if self==x then tp_rfn(tp_subst(x, v, base_tp), self, decls) else
    var self' := if (tm_fn(self, v)) then fresh_from([x]+tm_vars(v)+tp_vars(T)) else self;
    var decls' := if (self==self') then decls else decls_subst(self, tm_var(self'), decls);
    tp_rfn(tp_subst(x, v, base_tp), self', decls_subst(x, v, decls'))
  case tp_and(and1, and2) => tp_and(tp_subst(x, v, and1), tp_subst(x, v, and2))
  case tp_or(or1, or2) => tp_or(tp_subst(x, v, or1), tp_subst(x, v, or2))
  case tp_top => T
  case tp_bot => T
}
function def_subst(x: nat, v: tm, d: def): def
  decreases def_size(d), d;
  ensures v.tm_var? ==> def_size(d)==def_size(def_subst(x, v, d));
{
  match d
  case def_tm(l, t1) => def_tm(l, tm_subst(x, v, t1))
  case def_mt(m, param, body) =>
    if param==x then d else
    var param' := if (tm_fn(param, v)) then fresh_from([x]+tm_vars(v)+def_vars(d)) else param;
    var body' := if (param==param') then body else tm_subst(param, tm_var(param'), body);
    def_mt(m, param', tm_subst(x, v, body'))
}
function decl_subst(x: nat, v: tm, d: decl): decl
  decreases decl_size(d), d;
  ensures v.tm_var? ==> decl_size(d)==decl_size(decl_subst(x, v, d));
{
  match d
  case decl_tp(L, S, U, concrete) => decl_tp(L, tp_subst(x, v, S), tp_subst(x, v, U), concrete)
  case decl_tm(l, T) => decl_tm(l, tp_subst(x, v, T))
  case decl_mt(m, P, R) => decl_mt(m, tp_subst(x, v, P), tp_subst(x, v, R))
}
function defs_subst(x: nat, v: tm, defs: list<def>): list<def>
  decreases defs_size(defs), defs;
  ensures v.tm_var? ==> defs_size(defs)==defs_size(defs_subst(x, v, defs));
{
  match defs
  case Nil => Nil
  case Cons(head, tail) => Cons(def_subst(x, v, head), defs_subst(x, v, tail))
}
function decls_subst(x: nat, v: tm, decls: list<decl>): list<decl>
  decreases decls_size(decls), decls;
  ensures v.tm_var? ==> decls_size(decls)==decls_size(decls_subst(x, v, decls));
{
  match decls
  case Nil => Nil
  case Cons(head, tail) => Cons(decl_subst(x, v, head), decls_subst(x, v, tail))
}

// ### Free variables ###
// fn(x, A) <==> x appears free in A

predicate tm_fn(x: nat, t: tm)
{
  match t
  case tm_var(x') => x'==x
  case tm_new(y, Tc, init, t') => tp_fn(x, Tc) || (y!=x && (defs_fn(x, init) || tm_fn(x, t')))
  case tm_sel(t1, l) => tm_fn(x, t1)
  case tm_msel(o, m, a) => tm_fn(x, o) || tm_fn(x, a)
  case tm_loc(loc) => false
}
predicate tp_fn(x: nat, T: tp)
{
  match T
  case tp_sel(p, L, concrete) => tm_fn(x, p)
  case tp_rfn(base_tp, self, decls) => tp_fn(x, base_tp) || (self!=x && decls_fn(x, decls))
  case tp_and(and1, and2) => tp_fn(x, and1) || tp_fn(x, and2)
  case tp_or(or1, or2) => tp_fn(x, or1) || tp_fn(x, or2)
  case tp_top => false
  case tp_bot => false
}
predicate def_fn(x: nat, d: def)
{
  match d
  case def_tm(l, t1) => tm_fn(x, t1)
  case def_mt(m, param, body) => param!=x && tm_fn(x, body)
}
predicate decl_fn(x: nat, d: decl)
{
  match d
  case decl_tp(L, S, U, concrete) => tp_fn(x, S) || tp_fn(x, U)
  case decl_tm(l, T) => tp_fn(x, T)
  case decl_mt(m, P, R) => tp_fn(x, P) || tp_fn(x, R)
}
predicate defs_fn(x: nat, defs: list<def>)
{
  defs.Cons? && (def_fn(x, defs.head) || defs_fn(x, defs.tail))
}
predicate decls_fn(x: nat, decls: list<decl>)
{
  decls.Cons? && (decl_fn(x, decls.head) || decls_fn(x, decls.tail))
}

// ### Variables ###
function tm_vars(t: tm): seq<int>
  ensures forall x :: x in tm_vars(t) ==> x>=0;
{
  match t
  case tm_var(x') => [x']
  case tm_new(y, Tc, init, t') => [y]+tp_vars(Tc)+defs_vars(init)+tm_vars(t')
  case tm_sel(t1, l) => tm_vars(t1)
  case tm_msel(o, m, a) => tm_vars(o)+tm_vars(a)
  case tm_loc(loc) => []
}
function tp_vars(T: tp): seq<int>
  ensures forall x :: x in tp_vars(T) ==> x>=0;
{
  match T
  case tp_sel(p, L, concrete) => tm_vars(p)
  case tp_rfn(base_tp, self, decls) => tp_vars(base_tp)+[self]+decls_vars(decls)
  case tp_and(and1, and2) => tp_vars(and1)+tp_vars(and2)
  case tp_or(or1, or2) => tp_vars(or1)+tp_vars(or2)
  case tp_top => []
  case tp_bot => []
}
function def_vars(d: def): seq<int>
  ensures forall x :: x in def_vars(d) ==> x>=0;
{
  match d
  case def_tm(l, t1) => tm_vars(t1)
  case def_mt(m, param, body) => [param]+tm_vars(body)
}
function decl_vars(d: decl): seq<int>
  ensures forall x :: x in decl_vars(d) ==> x>=0;
{
  match d
  case decl_tp(L, S, U, concrete) => tp_vars(S)+tp_vars(U)
  case decl_tm(l, T) => tp_vars(T)
  case decl_mt(m, P, R) => tp_vars(P)+tp_vars(R)
}
function defs_vars(defs: list<def>): seq<int>
  ensures forall x :: x in defs_vars(defs) ==> x>=0;
{
  match defs
  case Nil => []
  case Cons(head, tail) => def_vars(head)+defs_vars(tail)
}
function decls_vars(decls: list<decl>): seq<int>
  ensures forall x :: x in decls_vars(decls) ==> x>=0;
{
  match decls
  case Nil => []
  case Cons(head, tail) => decl_vars(head)+decls_vars(tail)
}

// ### Reduction ###
function step(t: tm, s: store): option<pair<tm, store>>
{
  /* msel */
  if (t.tm_msel? && t.o.tm_loc? && value(t.a) && t.o.loc < |s.m| &&
     def_method_lookup(t.m, store_lookup(t.o.loc, s)).Some?)
  then Some(P(tm_subst(def_method_lookup(t.m, store_lookup(t.o.loc, s)).get.fst,
                       t.a,
                       def_method_lookup(t.m, store_lookup(t.o.loc, s)).get.snd),
              s))
  /* msel1 */
  else if (t.tm_msel? && step(t.o, s).Some?)
  then Some(P(tm_msel(step(t.o, s).get.fst, t.m, t.a), step(t.o, s).get.snd))
  /* msel2 */
  else if (t.tm_msel? && value(t.o) && step(t.a, s).Some?)
  then Some(P(tm_msel(t.o, t.m, step(t.a, s).get.fst), step(t.a, s).get.snd))
  /* sel */
  else if (t.tm_sel? && t.t.tm_loc? && t.t.loc < |s.m| &&
           def_field_lookup(t.l, store_lookup(t.t.loc, s)).Some?)
  then Some(P(def_field_lookup(t.l, store_lookup(t.t.loc, s)).get, s))
  /* sel1 */
  else if (t.tm_sel? && step(t.t, s).Some?)
  then Some(P(tm_sel(step(t.t, s).get.fst, t.l), step(t.t, s).get.snd))
  /* new */
  else if (t.tm_new?)
  then Some(P(tm_subst(t.y, tm_loc(|s.m|), t.t'),
              Store(s.m+[P(t.Tc, lst2seq(defs_subst(t.y, tm_loc(|s.m|), t.init)))])))
  else None
}

predicate irred(t: tm, s: store)
{
  step(t, s).None?
}

// ### Multi-steps ###
predicate mstep(t: tm, s: store, t': tm, s': store, n: nat)
  decreases n;
{
  if (n==0) then t==t' && s==s'
  else step(t, s).Some? && mstep(step(t, s).get.fst, step(t, s).get.snd, t', s', n-1)
}

// ### Properties of Operational Semantics ###

ghost method lemma_value__irred(t: tm, s: store)
  requires value(t);
  ensures irred(t, s);
{
}

ghost method lemma_mstep_trans(t1: tm, s1: store, t2: tm, s2: store, t3: tm, s3: store, n12: nat, n23: nat)
  requires mstep(t1, s1, t2, s2, n12);
  requires mstep(t2, s2, t3, s3, n23);
  ensures mstep(t1, s1, t3, s3, n12+n23);
  decreases n12+n23;
{
  if (n12>0) {
    lemma_mstep_trans(step(t1, s1).get.fst, step(t1, s1).get.snd, t2, s2, t3, s3, n12-1, n23);
  } else if (n23>0) {
    lemma_mstep_trans(step(t1, s1).get.fst, step(t1, s1).get.snd, step(t2, s2).get.fst, step(t2, s2).get.snd, t3, s3, n12, n23-1);
  }
}

ghost method lemma_mstep_trans'(t1: tm, s1: store, t2: tm, s2: store, t3: tm, s3: store, n12: nat, n13: nat)
  requires n12 <= n13;
  requires mstep(t1, s1, t2, s2, n12);
  requires mstep(t1, s1, t3, s3, n13);
  ensures mstep(t2, s2, t3, s3, n13-n12);
  decreases n12;
{
  if (n12>0 && n13>0) {
    lemma_mstep_trans'(step(t1, s1).get.fst, step(t1, s1).get.snd, t2, s2, t3, s3, n12-1, n13-1);
  }
}

// ### Congruence Lemmas ###

ghost method lemma_mstep_sel(o: tm, l: nat, o': tm, s: store, s': store, oi: nat)
  requires mstep(o, s, o', s', oi);
  ensures mstep(tm_sel(o, l), s, tm_sel(o', l), s', oi);
  decreases oi;
{
  if (oi>0) {
    lemma_mstep_sel(step(o, s).get.fst, l, o', step(o, s).get.snd, s', oi-1);
  }
}

ghost method lemma_sel_irred__o_mstep_irred(o: tm, l: nat, t': tm, s: store, s': store, i: nat) returns (o': tm, so': store, oi: nat)
  requires mstep(tm_sel(o, l), s, t', s', i);
  requires irred(t', s');
  ensures oi<=i && mstep(o, s, o', so', oi) && irred(o', so');
  decreases i;
{
  if (irred(o, s)) {
    o' := o;
	  so' := s;
    oi := 0;
  } else {
    assert step(o, s).Some?;
    lemma_mstep_trans'(tm_sel(o, l), s, tm_sel(step(o, s).get.fst, l), step(o, s).get.snd, t', s', 1, i);
    var o'', so'', oi' := lemma_sel_irred__o_mstep_irred(step(o, s).get.fst, l, t', step(o, s).get.snd, s', i-1);
    lemma_mstep_trans(o, s, step(o, s).get.fst, step(o, s).get.snd, o'', so'', 1, oi');
    o' := o'';
  	so' := so'';
    oi := oi'+1;
  }
}

// -----------
// Type System
// -----------

// ### Context ###
datatype context = Context(m: seq<pair<int,tp>>);
function context_extend(ctx: context, x: nat, T: tp): context
{
  Context([P(x, T)]+ctx.m)
}
function context_lookup(ctx: context, x: nat): option<tp>
  decreases |ctx.m|;
{
  if (|ctx.m|==0) then None
  else if (ctx.m[0].fst==x) then Some(ctx.m[0].snd)
  else context_lookup(Context(ctx.m[1..]), x)
}

// ### Orderings ###
predicate decl_lt(d1: decl, d2: decl)
{
  match d1
  case decl_tp(L1, S1, U1, concrete1) =>
    (match d2
     case decl_tp(L2, S2, U2, concrete2) =>
       (concrete1 && !concrete2) || (concrete1==concrete2 && L1<L2)
     case decl_tm(l2, T2) => true
     case decl_mt(m2, P2, R2) => true)
  case decl_tm(l1, T1) =>
    (match d2
     case decl_tp(L2, S2, U2, concrete2) => false
     case decl_tm(l2, T2) => l1<l2
     case decl_mt(m2, P2, R2) => true)
  case decl_mt(m1, P1, R1) =>
    (match d2
     case decl_tp(L2, S2, U2, concrete2) => false
     case decl_tm(l2, T2) => false
     case decl_mt(m2, P2, R2) => m1<m2)    
}
predicate decl_eq(d1: decl, d2: decl)
  ensures d1==d2 ==> decl_eq(d1, d2);
  ensures decl_eq(d1, d2) ==> decl_label(d1)==decl_label(d2);
  ensures decl_eq(d1, d2) ==> d1.decl_tp?==d2.decl_tp?;
  ensures decl_eq(d1, d2) ==> d1.decl_tm?==d2.decl_tm?;
  ensures decl_eq(d1, d2) ==> d1.decl_mt?==d2.decl_mt?;
  ensures decl_eq(d1, d2) ==> !decl_lt(d1, d2) && !decl_lt(d2, d1);
{
  match d1
  case decl_tp(L1, S1, U1, concrete1) => d2.decl_tp? && d2.concrete==concrete1 && d2.L==L1
  case decl_tm(l1, T1) => d2.decl_tm? && d2.l==l1
  case decl_mt(m1, P1, R1) => d2.decl_mt? && d2.m==m1
}
predicate decl_le(d1: decl, d2: decl)
  ensures d1==d2 ==> decl_le(d1, d2);
{
  decl_lt(d1, d2) || decl_eq(d1, d2)
}
predicate decl_seq_sorted(s: seq<decl>)
{
  forall m,n :: 0 <= m < n < |s| ==> decl_le(s[m], s[n])
}
function decl_seq_merge(s1: seq<decl>, s2: seq<decl>): seq<decl>
{
  if (s1 == []) then s2
  else if (s2 == []) then s1
  else if (decl_le(s1[0], s2[0])) then [s1[0]]+decl_seq_merge(s1[1..], s2)
  else [s2[0]]+decl_seq_merge(s1, s2[1..])
}
function decl_seq_sort(s: seq<decl>): seq<decl>
{
  if (s == []) then s else
    var i: nat := (|s|-1)/2;
    decl_seq_merge(decl_seq_sort(s[..i]), decl_seq_sort(s[i+1..]))
}
predicate def_lt(d1: def, d2: def)
{
  match d1
  case def_tm(l1, t1) =>
    (match d2
     case def_tm(l2, t2) => l1<l2
     case def_mt(m2, param2, body2) => true)
  case def_mt(m1, param1, body1) =>
    (match d2
     case def_tm(l2, t2) => false
     case def_mt(m2, param2, body2) => m1<m2)
}
predicate def_eq(d1: def, d2: def)
  ensures d1==d2 ==> def_eq(d1, d2);
{
  match d1
  case def_tm(l1, t1) => d2.def_tm? && d2.l==l1
  case def_mt(m1, param1, body1) => d2.def_mt? && d2.m==m1
}
predicate def_le(d1: def, d2: def)
  ensures d1==d2 ==> def_le(d1, d2);
{
  def_lt(d1, d2) || def_eq(d1, d2)
}
predicate def_seq_sorted(s: seq<def>)
{
  forall m,n :: 0 <= m < n < |s| ==> def_le(s[m], s[n])
}
function def_seq_merge(s1: seq<def>, s2: seq<def>): seq<def>
{
  if (s1 == []) then s2
  else if (s2 == []) then s1
  else if (def_le(s1[0], s2[0])) then [s1[0]]+def_seq_merge(s1[1..], s2)
  else [s2[0]]+def_seq_merge(s1, s2[1..])
}
function def_seq_sort(s: seq<def>): seq<def>
{
  if (s == []) then s else
    var i: nat := (|s|-1)/2;
    def_seq_merge(def_seq_sort(s[..i]), def_seq_sort(s[i+1..]))
}

// ### Declaration Lattice ###
predicate decl_bot(d: decl)
{
  match d
  case decl_tp(L, S, U, concrete) => S==tp_top && U==tp_bot
  case decl_tm(l, T) => T==tp_bot
  case decl_mt(m, S, U) => S==tp_top && U==tp_bot
}
function decl_and(d1: decl, d2: decl): decl
  requires decl_eq(d1, d2);
  ensures decl_eq(d1, decl_and(d1, d2));
  ensures decl_eq(d2, decl_and(d1, d2));
{
  match d1
  case decl_tp(L, S, U, concrete) => decl_tp(L, tp_or(S, d2.S), tp_and(U, d2.U), concrete)
  case decl_tm(l, U) => decl_tm(l, tp_and(U, d2.T))
  case decl_mt(m, S, U) => decl_mt(m, tp_or(S, d2.P), tp_and(U, d2.R))
}
function decl_or(d1: decl, d2: decl): decl
  requires decl_eq(d1, d2);
  ensures decl_eq(d1, decl_or(d1, d2));
  ensures decl_eq(d2, decl_or(d1, d2));
{
  match d1
  case decl_tp(L, S, U, concrete) => decl_tp(L, tp_and(S, d2.S), tp_or(U, d2.U), concrete)
  case decl_tm(l, U) => decl_tm(l, tp_or(U, d2.T))
  case decl_mt(m, S, U) => decl_mt(m, tp_and(S, d2.P), tp_or(U, d2.R))
}
function decls_fin_and(s1: seq<decl>, s2: seq<decl>): seq<decl>
{
        if (s1 == []) then s2
  else  if (s2 == []) then s1
  else  if (decl_eq(s1[0], s2[0])) then   [decl_and(s1[0], s2[0])]+decls_fin_and(s1[1..], s2[1..])
  else  if (decl_lt(s1[0], s2[0])) then   [s1[0]]+decls_fin_and(s1[1..], s2)
  else/*if (decl_lt(s2[0], s1[0])) then*/ [s2[0]]+decls_fin_and(s1, s2[1..])
}
function decls_and(Ds1: decls, Ds2: decls): decls
{
  match Ds1
  case decls_bot => decls_bot
  case decls_fin(s1) =>
    (match Ds2
     case decls_bot => decls_bot
     case decls_fin(s2) => decls_fin(seq2lst(decls_fin_and(lst2seq(s1), lst2seq(s2)))))
}
function decls_fin_or(s1: seq<decl>, s2: seq<decl>): seq<decl>
{
        if (s1 == []) then []
  else  if (s2 == []) then []
  else  if (decl_eq(s1[0], s2[0])) then   [decl_or(s1[0], s2[0])]+decls_fin_and(s1[1..], s2[1..])
  else  if (decl_lt(s1[0], s2[0])) then   decls_fin_or(s1[1..], s2)
  else/*if (decl_lt(s2[0], s1[0])) then*/ decls_fin_or(s1, s2[1..])
}
function decls_or(Ds1: decls, Ds2: decls): decls
{
  match Ds1
  case decls_bot => Ds2
  case decls_fin(s1) =>
    (match Ds2
     case decls_bot => Ds1
     case decls_fin(s2) => decls_fin(seq2lst(decls_fin_or(lst2seq(s1), lst2seq(s2)))))
}

// ### Typing-Related Judgments ###

predicate typing(n: nat, ctx: context, s: store, t: tm, T: tp)
  decreases n;
{
  match t
  case tm_var(x) => context_lookup(ctx, x)==Some(T)
  case tm_new(y, Tc, init, t') =>
    n>0 && is_concrete(Tc) &&
    exists Ds:decls :: Ds.decls_fin? &&
    wfe_type(n-1, ctx, s, Tc) &&
    expansion(n-1, ctx, s, y, Tc, Ds) && 
    wf_init(n-1, false, context_extend(ctx, y, Tc), s, lst2seq(Ds.decls), def_seq_sort(lst2seq(init))) &&
    !tp_fn(y, T) &&
    exists T' :: typing(n-1, context_extend(ctx, y, Tc), s, t', T') &&
    subtype(n-1, context_extend(ctx, y, Tc), s, T', T)
  case tm_sel(t, l) =>
    n>0 && field_membership(n-1, ctx, s, t, l, T)
  case tm_msel(o, m, a) =>
    n>0 && exists S, T' :: method_membership(n-1, ctx, s, o, m, S, T) &&
    typing(n-1, ctx, s, a, T') &&
    subtype(n-1, ctx, s, T', S)
  case tm_loc(loc) => loc < |s.m| && store_lookup_type(loc, s)==T
}
predicate wf_init(n: nat, already_in_store: bool, ctx: context, s: store, decls: seq<decl>, defs: seq<def>)
  decreases n;
{
  n>0 && (
  (decls==[] && defs==[]) || (|decls|>0 && (
    ((decls[0].decl_tp? && subtype(n-1, ctx, s, decls[0].S, decls[0].U)) &&
     wf_init(n-1, already_in_store, ctx, s, decls[1..], defs)) || (|defs|>0 && (
    ((decls[0].decl_tm? && defs[0].def_tm? && decls[0].l==defs[0].l &&
      (if already_in_store then value(defs[0].t) else syn_value(defs[0].t)) &&
      exists T :: typing(n-1, ctx, s, defs[0].t, T) &&
      subtype(n-1, ctx, s, T, decls[0].T)) ||
     (decls[0].decl_mt? && defs[0].def_mt? && decls[0].m==defs[0].m &&
      wfe_type(n-1, ctx, s, decls[0].P) &&
      exists T' :: typing(n-1, context_extend(ctx, defs[0].param, decls[0].P), s, defs[0].body, T') &&
      subtype(n-1, context_extend(ctx, defs[0].param, decls[0].P), s, T', decls[0].R))) &&
     wf_init(n-1, already_in_store, ctx, s, decls[1..], defs[1..])))))
  )
}
predicate wf_decl(n: nat, ctx: context, s: store, d: decl)
  decreases n;
{
  match d
  case decl_tp(L, S, U, concrete) => n>0 && wf_type(n-1, ctx, s, S) && wf_type(n-1, ctx, s, U) &&
    (!concrete || (S==tp_bot && is_concrete(U)))
  case decl_tm(l, T) => n>0 && wf_type(n-1, ctx, s, T)
  case decl_mt(m, S, T) => n>0 && wf_type(n-1, ctx, s, S) && wf_type(n-1, ctx, s, T)
}
predicate wf_decls(n: nat, ctx: context, s: store, Ds: seq<decl>)
  decreases n;
{
  forall d :: d in Ds ==> n>0 && wf_decl(n-1, ctx, s, d)
}
predicate wf_type(n: nat, ctx: context, s: store, T: tp)
  decreases n;
{
  match T
  case tp_rfn(T', z, Ds) =>
    n>0 && wf_type(n-1, ctx, s, T') && wf_decls(n-1, context_extend(ctx, z, T), s, lst2seq(Ds))
  case tp_sel(p, L, concrete) =>
    path(p) &&
    n>0 && exists S, U :: type_membership(n-1, ctx, s, p, L, concrete, S, U)
  case tp_and(T1, T2) => n>0 && wf_type(n-1, ctx, s, T1) && wf_type(n-1, ctx, s, T2)
  case tp_or(T1, T2) => n>0 && wf_type(n-1, ctx, s, T1) && wf_type(n-1, ctx, s, T2)
  case tp_top => true
  case tp_bot => true
}
predicate wfe_type(n: nat, ctx: context, s: store, T: tp)
  decreases n;
{
  n>0 && wf_type(n-1, ctx, s, T) && exists Ds :: expansion(n-1, ctx, s, 0, T, Ds)
}
predicate membership(n: nat, ctx: context, s: store, t: tm, l: nat, d: decl)
  decreases n;
{
  decl_label(d)==l &&
  n>0 && exists T :: typing(n-1, ctx, s, t, T) &&
  forall z:nat :: !tp_fn(z, T) && context_lookup(ctx, z).None? && !tm_fn(z, t) ==>
  exists Ds ::
  expansion(n-1, ctx, s, z, T, Ds) &&
  ((Ds.decls_fin? &&
     ((path(t) && exists d' :: d' in lst2seq(Ds.decls) && d==decl_subst(z, t, d')) ||
     (!path(t) && exists d' :: d' in lst2seq(Ds.decls) && !decl_fn(z, d') &&
       decl_eq(d', d) && decl_sub(n-1, context_extend(ctx, z, T), s, d', d)))) ||
   (Ds.decls_bot? && decl_bot(d)))
}
predicate field_membership(n: nat, ctx: context, s: store, t: tm, l: nat, T: tp)
  decreases n;
{
  n>0 && membership(n-1, ctx, s, t, l, decl_tm(l, T))
}
predicate method_membership(n: nat, ctx: context, s: store, t: tm, m: nat, P: tp, R: tp)
  decreases n;
{
  n>0 && exists d :: membership(n-1, ctx, s, t, m, d) &&
  d.decl_mt? && d.m==m && d.P==P && d.R==R
}
predicate type_membership(n: nat, ctx: context, s: store, t: tm, L: nat, concrete: bool, S: tp, U: tp)
  decreases n;
{
  n>0 && exists d :: membership(n-1, ctx, s, t, L, d) &&
  d.decl_tp? && d.L==L && d.concrete==concrete && d.S==S && d.U==U
}
predicate m_decl_seq_sorted(m: seq<pair<tp, decls>>)
{
  forall p :: p in m && p.snd.decls_fin? ==> decl_seq_sorted(lst2seq(p.snd.decls))
}
function lookup<K,V>(k: K, m: seq<pair<K,V>>): option<V>
{
  if (exists v :: P(k,v) in m)
  then (var v :| P(k, v) in m; Some(v))
  else None
}

predicate expansion(n: nat, ctx: context, s: store, z: nat, T: tp, Ds: decls)
  decreases n;
{
  n>0 && expansion_iter(n-1, [], ctx, s, z, T, Ds)
}
predicate expansion_iter(n: nat, m: seq<pair<tp, decls>>, ctx: context, s: store, z: nat, T: tp, Ds: decls)
  decreases n;
{
  match T
  case tp_rfn(T', z', Ds') =>
    n>0 &&
    exists DsT' :: expansion_iter(n-1, m, ctx, s, z, T', DsT') &&
    exists rfn_decls :: rfn_decls==decl_seq_sort(lst2seq(decls_subst(z', tm_var(z), Ds'))) &&
    Ds==decls_and(decls_fin(seq2lst(rfn_decls)), DsT')
  case tp_sel(p, L, concrete) =>
    (lookup(T, m).Some? && lookup(T, m).get==Ds) || 
    (n>0 && lookup(T, m).None? && exists S, U :: type_membership(n-1, ctx, s, p, L, concrete, S, U) &&
    expansion_fix(n-1, T, decls_fin(Nil), m, ctx, s, z, U, Ds))
  case tp_and(T1, T2) =>
    n>0 &&
    exists Ds1, Ds2 :: expansion_iter(n-1, m, ctx, s, z, T1, Ds1) &&
                       expansion_iter(n-1, m, ctx, s, z, T2, Ds2) &&
    Ds==decls_and(Ds1, Ds2)
  case tp_or(T1, T2) =>
    n>0 &&
    exists Ds1, Ds2 :: expansion_iter(n-1, m, ctx, s, z, T1, Ds1) &&
                       expansion_iter(n-1, m, ctx, s, z, T2, Ds2) &&
    Ds==decls_or(Ds1, Ds2)
  case tp_top => Ds==decls_fin(Nil)
  case tp_bot => Ds==decls_bot
}
predicate expansion_fix(n: nat, selT: tp, selDs: decls, m: seq<pair<tp, decls>>, ctx: context, s: store, z: nat, T: tp, Ds: decls)
  decreases n;
{
  n>0 && (
  (selDs==Ds && expansion_iter(n-1, [P(selT, selDs)]+m, ctx, s, z, T, Ds)) ||
  (selDs!=Ds && exists Da :: expansion_iter(n-1, [P(selT, selDs)]+m, ctx, s, z, T, Da) &&
   expansion_fix(n-1, selT, Da, m, ctx, s, z, T, Ds)))
}
predicate decl_sub(n: nat, ctx: context, s: store, d1: decl, d2: decl)
  requires decl_eq(d1, d2);
  decreases n;
{
  match d1
  case decl_tp(L, S, U, concrete) => n>0 && subtype(n-1, ctx, s, d2.S, S) && subtype(n-1, ctx, s, U, d2.U)
  case decl_tm(l, U) => n>0 && subtype(n-1, ctx, s, U, d2.T)
  case decl_mt(m, S, U) => n>0 && subtype(n-1, ctx, s, d2.P, S) && subtype(n-1, ctx, s, U, d2.R)
}
predicate decls_fin_sub(n: nat, ctx: context, s: store, s1: seq<decl>, s2: seq<decl>)
  decreases n;
{
  (s1 == [] && s2 == []) ||
  (|s1|>0 && |s2|>0 && n>0 && (
  (decl_eq(s1[0], s2[0]) && decl_sub(n-1, ctx, s, s1[0], s2[0]) &&
   decls_fin_sub(n-1, ctx, s, s1[1..], s2[1..])) ||
  (decl_lt(s1[0], s2[0]) && decls_fin_sub(n-1, ctx, s, s1[1..], s2))))
}
predicate decls_sub(n: nat, ctx: context, s: store, Ds1: decls, Ds2: decls)
  decreases n;
{
  match Ds1
  case decls_bot => true
  case decls_fin(s1) =>
    (match Ds2
     case decls_bot => false
     case decls_fin(s2) => n>0 && decls_fin_sub(n-1, ctx, s, lst2seq(s1), lst2seq(s2)))
}
predicate path_red(ctx: context, s: store, p1: tm, p2: tm)
{
  path(p1) && path(p2) && (
  (p1.tm_sel? && p1.t.tm_loc? && p2.tm_loc? && p1.t.loc < |s.m| &&
   def_field_lookup(p1.l, store_lookup(p1.t.loc, s)).Some? &&
   p2==def_field_lookup(p1.l, store_lookup(p1.t.loc, s)).get) ||
  (p1.tm_sel? && p2.tm_sel? && p1.l==p2.l && path_red(ctx, s, p1.t, p2.t)))
}

predicate subtype(n: nat, ctx: context, s: store, S: tp, T: tp)
  decreases n;
{
  n>0 && (
  /* refl */    (S==T && wfe_type(n-1, ctx, s, T)) ||
  /* <:-top */  (T.tp_top? && wfe_type(n-1, ctx, s, S)) ||
  /* bot-<: */  (S.tp_bot? && wfe_type(n-1, ctx, s, T)) ||
  /* <:-rfn */  (T.tp_rfn? && wfe_type(n-1, ctx, s, T) && subtype(n-1, ctx, s, S, T.base_tp) &&
                 exists Ds' :: expansion(n-1, ctx, s, T.self, S, Ds') &&
                 exists rfn_decls :: rfn_decls==decl_seq_sort(lst2seq(T.decls)) &&
                 decls_sub(n-1, context_extend(ctx, T.self, S), s, decls_fin(seq2lst(rfn_decls)), Ds')) ||
  /* rfn-<: */  (S.tp_rfn? && wfe_type(n-1, ctx, s, S) && subtype(n-1, ctx, s, S.base_tp, T)) ||
  /* <:-sel */  (T.tp_sel? &&
                 exists S', U' :: type_membership(n-1, ctx, s, T.p, T.L, T.concrete, S', U') &&
                 subtype(n-1, ctx, s, S', U') && subtype(n-1, ctx, s, S, S')) ||
  /* sel-<: */  (S.tp_sel? &&
                 exists S', U' :: type_membership(n-1, ctx, s, S.p, S.L, S.concrete, S', U') &&
                 subtype(n-1, ctx, s, S', U') && subtype(n-1, ctx, s, U', T)) ||
  /* <:-and */  (T.tp_and? && subtype(n-1, ctx, s, S, T.and1) && subtype(n-1, ctx, s, S, T.and2)) ||
  /* and1-<: */ (S.tp_and? && wfe_type(n-1, ctx, s, S.and2) && subtype(n-1, ctx, s, S.and1, T)) ||
  /* and2-<: */ (S.tp_and? && wfe_type(n-1, ctx, s, S.and1) && subtype(n-1, ctx, s, S.and2, T)) ||
  /* <:-or1 */  (T.tp_or? && wfe_type(n-1, ctx, s, T.or2) && subtype(n-1, ctx, s, S, T.or1)) ||
  /* <:-or2 */  (T.tp_or? && wfe_type(n-1, ctx, s, T.or1) && subtype(n-1, ctx, s, S, T.or2)) ||
  /* or-<: */   (S.tp_or? && subtype(n-1, ctx, s, S.or1, T) && subtype(n-1, ctx, s, S.or2, T)) ||
  /* pathred */ (T.tp_sel? && wfe_type(n-1, ctx, s, T) && exists p :: path_red(ctx, s, T.p, p) &&
                 subtype(n-1, ctx, s, S, tp_sel(p, T.L, T.concrete))))
}

predicate typing'(ctx: context, s: store, t: tm, T: tp)
{
  exists n:nat :: typing(n, ctx, s, t, T)
}
predicate wf_init'(already_in_store: bool, ctx: context, s: store, decls: seq<decl>, defs: seq<def>)
{
  exists n:nat :: wf_init(n, already_in_store, ctx, s, decls, defs)
}
predicate wfe_type'(ctx: context, s: store, T: tp)
{
  exists n:nat :: wfe_type(n, ctx, s, T)
}
predicate membership'(ctx: context, s: store, t: tm, l: nat, d: decl)
{
  exists n:nat :: membership(n, ctx, s, t, l, d)
}
predicate field_membership'(ctx: context, s: store, t: tm, l: nat, T: tp)
{
  exists n:nat :: field_membership(n, ctx, s, t, l, T)
}
predicate method_membership'(ctx: context, s: store, t: tm, m: nat, P: tp, R: tp)
{
  exists n:nat :: method_membership(n, ctx, s, t, m, P, R)
}
predicate expansion'(ctx: context, s: store, z: nat, T: tp, Ds: decls)
{
  exists n:nat :: expansion(n, ctx, s, z, T, Ds)
}
predicate decl_sub'(ctx: context, s: store, d1: decl, d2: decl)
  requires decl_eq(d1, d2);
{
  exists n:nat :: decl_sub(n, ctx, s, d1, d2)
}
predicate subtype'(ctx: context, s: store, S: tp, T: tp)
{
  exists n:nat :: subtype(n, ctx, s, S, T)
}

// ### Properties about typing-related judgments ###
function typing_n(ctx: context, s: store, t: tm, T: tp): nat
  requires typing'(ctx, s, t, T);
  ensures typing(typing_n(ctx, s, t, T), ctx, s, t, T);
{
  var n:nat :| typing(n, ctx, s, t, T); n
}
function wf_init_n(already_in_store: bool, ctx: context, s: store, decls: seq<decl>, defs: seq<def>): nat
  requires wf_init'(already_in_store, ctx, s, decls, defs);
  ensures wf_init(wf_init_n(already_in_store, ctx, s, decls, defs), already_in_store, ctx, s, decls, defs);
{
  var n:nat :| wf_init(n, already_in_store, ctx, s, decls, defs); n
}
function wfe_type_n(ctx: context, s: store, T: tp): nat
  requires wfe_type'(ctx, s, T);
  ensures wfe_type(wfe_type_n(ctx, s, T), ctx, s, T);
{
  var n:nat :| wfe_type(n, ctx, s, T); n
}
function field_membership_n(ctx: context, s: store, t: tm, l: nat, T: tp): nat
  requires field_membership'(ctx, s, t, l, T);
  ensures field_membership(field_membership_n(ctx, s, t, l, T), ctx, s, t, l, T);
{
  var n:nat :| field_membership(n, ctx, s, t, l, T); n
}
function method_membership_n(ctx: context, s: store, t: tm, m: nat, P: tp, R: tp): nat
  requires method_membership'(ctx, s, t, m, P, R);
  ensures method_membership(method_membership_n(ctx, s, t, m, P, R), ctx, s, t, m, P, R);
{
  var n:nat :| method_membership(n, ctx, s, t, m, P, R); n
}
function expansion_n(ctx: context, s: store, z: nat, T: tp, Ds: decls): nat
  requires expansion'(ctx, s, z, T, Ds);
  ensures expansion(expansion_n(ctx, s, z, T, Ds), ctx, s, z, T, Ds);
{
  var n:nat :| expansion(n, ctx, s, z, T, Ds); n
}
function subtype_n(ctx: context, s: store, S: tp, T: tp): nat
  requires subtype'(ctx, s, S, T);
  ensures subtype(subtype_n(ctx, s, S, T), ctx, s, S, T);
{
  var n:nat :| subtype(n, ctx, s, S, T); n
}

ghost method lemma_typing_monotonic(n: nat, ctx: context, s: store, t: tm, T: tp)
  requires typing(n, ctx, s, t, T);
  ensures typing(n+1, ctx, s, t, T);
{
  if (t.tm_var?) {
    assert typing(n+1, ctx, s, t, T);
  } else if (t.tm_new?) {
    if (n>0) {
      var Ds:decls :| Ds.decls_fin? &&
      wfe_type(n-1, ctx, s, t.Tc) &&
      expansion(n-1, ctx, s, t.y, t.Tc, Ds) && 
      wf_init(n-1, false, context_extend(ctx, t.y, t.Tc), s, lst2seq(Ds.decls), def_seq_sort(lst2seq(t.init))) &&
      !tp_fn(t.y, T) &&
      exists T' :: typing(n-1, context_extend(ctx, t.y, t.Tc), s, t.t', T') &&
      subtype(n-1, context_extend(ctx, t.y, t.Tc), s, T', T);

      var T':tp :|  typing(n-1, context_extend(ctx, t.y, t.Tc), s, t.t', T') &&
      subtype(n-1, context_extend(ctx, t.y, t.Tc), s, T', T);

      lemma_wfe_type_monotonic(n-1, ctx, s, t.Tc);
      lemma_expansion_monotonic(n-1, ctx, s, t.y, t.Tc, Ds); 
      lemma_wf_init_monotonic(n-1, false, context_extend(ctx, t.y, t.Tc), s, lst2seq(Ds.decls), def_seq_sort(lst2seq(t.init)));
      lemma_typing_monotonic(n-1, context_extend(ctx, t.y, t.Tc), s, t.t', T');
      lemma_subtype_monotonic(n-1, context_extend(ctx, t.y, t.Tc), s, T', T);
    }
  } else if (t.tm_sel?) {
    if (n>0) {
      lemma_field_membership_monotonic(n-1, ctx, s, t.t, t.l, T);
    }
  } else if (t.tm_msel?) {
    if (n>0) {
      var S, T' :| method_membership(n-1, ctx, s, t.o, t.m, S, T) &&
      typing(n-1, ctx, s, t.a, T') &&
      subtype(n-1, ctx, s, T', S);

      lemma_method_membership_monotonic(n-1, ctx, s, t.o, t.m, S, T);
      lemma_typing_monotonic(n-1, ctx, s, t.a, T');
      lemma_subtype_monotonic(n-1, ctx, s, T', S);

      assert method_membership(n, ctx, s, t.o, t.m, S, T) &&
      typing(n, ctx, s, t.a, T') &&
      subtype(n, ctx, s, T', S);

      helper_assert_exists_method_membership(n, ctx, s, t, T, S, T');
    }
  }
}
ghost method helper_assert_exists_method_membership(n: nat, ctx: context, s: store, t: tm, T: tp, S: tp, T': tp)
  requires t.tm_msel?;
  requires method_membership(n, ctx, s, t.o, t.m, S, T) &&
      typing(n, ctx, s, t.a, T') &&
      subtype(n, ctx, s, T', S);
  ensures exists S, T' :: method_membership(n, ctx, s, t.o, t.m, S, T) &&
      typing(n, ctx, s, t.a, T') &&
      subtype(n, ctx, s, T', S);
{
}
ghost method lemma_wf_init_monotonic(n: nat, already_in_store: bool, ctx: context, s: store, decls: seq<decl>, defs: seq<def>)
  requires wf_init(n, already_in_store, ctx, s, decls, defs);
  ensures wf_init(n+1, already_in_store, ctx, s, decls, defs);
{
  assume wf_init(n+1, already_in_store, ctx, s, decls, defs); // TODO
}
ghost method lemma_wfe_type_monotonic(n: nat, ctx: context, s: store, T: tp)
  requires wfe_type(n, ctx, s, T);
  ensures wfe_type(n+1, ctx, s, T);
{
  assume wfe_type(n+1, ctx, s, T); // TODO
}
ghost method lemma_field_membership_monotonic(n: nat, ctx: context, s: store, t: tm, l: nat, T: tp)
  requires field_membership(n, ctx, s, t, l, T);
  ensures field_membership(n+1, ctx, s, t, l, T);
{
  assume field_membership(n+1, ctx, s, t, l, T); // TODO
}
ghost method lemma_method_membership_monotonic(n: nat, ctx: context, s: store, t: tm, m: nat, P: tp, R: tp)
  requires method_membership(n, ctx, s, t, m, P, R);
  ensures method_membership(n+1, ctx, s, t, m, P, R);
{
  assume method_membership(n+1, ctx, s, t, m, P, R); // TODO
}
ghost method lemma_expansion_monotonic(n: nat, ctx: context, s: store, z: nat, T: tp, Ds: decls)
  requires expansion(n, ctx, s, z, T, Ds);
  ensures expansion(n+1, ctx, s, z, T, Ds);
{
  assume expansion(n+1, ctx, s, z, T, Ds); // TODO
}
ghost method lemma_subtype_monotonic(n: nat, ctx: context, s: store, S: tp, T: tp)
  requires subtype(n, ctx, s, S, T);
  ensures subtype(n+1, ctx, s, S, T);
{
  assume subtype(n+1, ctx, s, S, T); // TODO
}

// ----------
// Properties
// ----------

predicate store_extends<A>(s': store, s: store)
{
  |s.m|<=|s'.m| && forall l:nat :: l < |s.m| ==> s.m[l]==s'.m[l]
}
predicate store_well_typed1(s: store, loc: nat, y: nat, Tc: tp, init: seq<def>)
{
    exists n:nat :: n>0 &&
    is_concrete(Tc) &&
    exists Ds:decls :: Ds.decls_fin? &&
    wfe_type(n-1, Context([]), s, Tc) &&
    expansion(n-1, Context([]), s, y, Tc, Ds) && 
    wf_init(n-1, true, Context([]), s, lst2seq(decls_subst(y, tm_loc(loc), Ds.decls)), def_seq_sort(init))
}
predicate store_well_typed(s: store)
{
  forall l:nat :: l < |s.m| ==> store_well_typed1(s, l, fresh_from([]), store_lookup_type(l, s), store_lookup(l, s))
}
ghost method lemma_store_invariance_typing(n: nat, ctx: context, s: store, s': store, t: tm, T: tp)
  requires store_extends(s', s);
  requires typing(n, ctx, s, t, T);
  ensures typing(n, ctx, s', t, T);
  decreases t;
{
  if (t.tm_sel?) {
    lemma_store_invariance_membership(n-2, ctx, s, s', t.t, t.l, decl_tm(t.l, T));
  } else if (t.tm_msel?) {
    var S, T' :| method_membership(n-1, ctx, s, t.o, t.m, S, T) &&
    typing(n-1, ctx, s, t.a, T') &&
    subtype(n-1, ctx, s, T', S);
    lemma_store_invariance_membership(n-2, ctx, s, s', t.o, t.m, decl_mt(t.m, S, T));
    lemma_store_invariance_typing(n-1, ctx, s, s', t.a, T');
    lemma_store_invariance_subtype(n-1, ctx, s, s', T', S);
    assert method_membership(n-1, ctx, s', t.o, t.m, S, T) &&
    typing(n-1, ctx, s', t.a, T') &&
    subtype(n-1, ctx, s', T', S);
    helper_assert_exists_method_membership(n-1, ctx, s', t, T, S, T');
  } else if (t.tm_new?) {
    var Ds:decls, T' :| Ds.decls_fin? &&
    wfe_type(n-1, ctx, s, t.Tc) &&
    expansion(n-1, ctx, s, t.y, t.Tc, Ds) && 
    wf_init(n-1, false, context_extend(ctx, t.y, t.Tc), s, lst2seq(Ds.decls), def_seq_sort(lst2seq(t.init))) &&
    !tp_fn(t.y, T) &&
    typing(n-1, context_extend(ctx, t.y, t.Tc), s, t.t', T') &&
    subtype(n-1, context_extend(ctx, t.y, t.Tc), s, T', T);
    lemma_store_invariance_wfe_type(n-1, ctx, s, s', t.Tc);
    lemma_store_invariance_expansion(n-1, ctx, s, s', t.y, t.Tc, Ds); 
    lemma_store_invariance_wf_init(n-1, false, context_extend(ctx, t.y, t.Tc), s, s', lst2seq(Ds.decls), def_seq_sort(lst2seq(t.init)));
    lemma_store_invariance_typing(n-1, context_extend(ctx, t.y, t.Tc), s, s', t.t', T');
    lemma_store_invariance_subtype(n-1, context_extend(ctx, t.y, t.Tc), s, s', T', T);
    assert Ds.decls_fin? &&
    wfe_type(n-1, ctx, s', t.Tc) &&
    expansion(n-1, ctx, s', t.y, t.Tc, Ds) && 
    wf_init(n-1, false, context_extend(ctx, t.y, t.Tc), s', lst2seq(Ds.decls), def_seq_sort(lst2seq(t.init))) &&
    !tp_fn(t.y, T) &&
    typing(n-1, context_extend(ctx, t.y, t.Tc), s', t.t', T') &&
    subtype(n-1, context_extend(ctx, t.y, t.Tc), s', T', T);
    helper_assert_exists_new(n-1, ctx, s', t, T, Ds, T');
  } else {
  }
}
ghost method helper_assert_exists_new(n: nat, ctx: context, s: store, t: tm, T: tp, Ds: decls, T': tp)
  requires t.tm_new?;
  requires Ds.decls_fin? &&
    wfe_type(n, ctx, s, t.Tc) &&
    expansion(n, ctx, s, t.y, t.Tc, Ds) && 
    wf_init(n, false, context_extend(ctx, t.y, t.Tc), s, lst2seq(Ds.decls), def_seq_sort(lst2seq(t.init))) &&
    !tp_fn(t.y, T) &&
    typing(n, context_extend(ctx, t.y, t.Tc), s, t.t', T') &&
    subtype(n, context_extend(ctx, t.y, t.Tc), s, T', T);
  ensures exists Ds:decls, T' :: Ds.decls_fin? &&
    wfe_type(n, ctx, s, t.Tc) &&
    expansion(n, ctx, s, t.y, t.Tc, Ds) && 
    wf_init(n, false, context_extend(ctx, t.y, t.Tc), s, lst2seq(Ds.decls), def_seq_sort(lst2seq(t.init))) &&
    !tp_fn(t.y, T) &&
    typing(n, context_extend(ctx, t.y, t.Tc), s, t.t', T') &&
    subtype(n, context_extend(ctx, t.y, t.Tc), s, T', T);
{
}
ghost method lemma_store_invariance_membership(n: nat, ctx: context, s: store, s': store, t: tm, l: nat, d: decl)
  requires store_extends(s', s);
  requires membership(n, ctx, s, t, l, d);
  ensures membership(n, ctx, s', t, l, d);
{
  assume membership(n, ctx, s', t, l, d); // TODO
}
ghost method lemma_store_invariance_subtype(n: nat, ctx: context, s: store, s': store, S: tp, T: tp)
  requires store_extends(s', s);
  requires subtype(n, ctx, s, S, T);
  ensures subtype(n, ctx, s', S, T);
{
  assume subtype(n, ctx, s', S, T); // TODO
}
ghost method lemma_store_invariance_wfe_type(n: nat, ctx: context, s: store, s': store, T: tp)
  requires store_extends(s', s);
  requires wfe_type(n, ctx, s, T);
  ensures wfe_type(n, ctx, s', T);
{
  assume wfe_type(n, ctx, s', T); // TODO
}
ghost method lemma_store_invariance_expansion(n: nat, ctx: context, s: store, s': store, z: nat, T: tp, Ds: decls)
  requires store_extends(s', s);
  requires expansion(n, ctx, s, z, T, Ds);
  ensures expansion(n, ctx, s', z, T, Ds);
{
  assume expansion(n, ctx, s', z, T, Ds);
}
ghost method lemma_store_invariance_wf_init(n: nat, already_in_store: bool, ctx: context, s: store, s': store, decls: seq<decl>, defs: seq<def>)
  requires store_extends(s', s);
  requires wf_init(n, already_in_store, ctx, s, decls, defs);
  ensures wf_init(n, already_in_store, ctx, s', decls, defs);
{
  assume wf_init(n, already_in_store, ctx, s', decls, defs);
}
ghost method lemma_store_invariance_well_typed1(s: store, s': store, loc: nat, y: nat, Tc: tp, init: seq<def>)
  requires store_extends(s', s);
  requires store_well_typed1(s, loc, y, Tc, init);
  ensures store_well_typed1(s', loc, y, Tc, init);
{
  var n:nat, Ds:decls :| n>0 &&
    is_concrete(Tc) &&
    Ds.decls_fin? &&
    wfe_type(n-1, Context([]), s, Tc) &&
    expansion(n-1, Context([]), s, y, Tc, Ds) && 
    wf_init(n-1, true, Context([]), s, lst2seq(decls_subst(y, tm_loc(loc), Ds.decls)), def_seq_sort(init));
  lemma_store_invariance_wfe_type(n-1, Context([]), s, s', Tc);
  lemma_store_invariance_expansion(n-1, Context([]), s, s', y, Tc, Ds); 
  lemma_store_invariance_wf_init(n-1, true, Context([]), s, s', lst2seq(decls_subst(y, tm_loc(loc), Ds.decls)), def_seq_sort(init));
  assert n>0 &&
    is_concrete(Tc) &&
    Ds.decls_fin? &&
    wfe_type(n-1, Context([]), s', Tc) &&
    expansion(n-1, Context([]), s', y, Tc, Ds) && 
    wf_init(n-1, true, Context([]), s', lst2seq(decls_subst(y, tm_loc(loc), Ds.decls)), def_seq_sort(init));
  helper_assert_exists_store_well_typed1(s', loc, y, Tc, init, n, Ds);
}
ghost method helper_assert_exists_store_well_typed1(s: store, loc: nat, y: nat, Tc: tp, init: seq<def>, n: nat, Ds: decls)
  requires n>0 &&
    is_concrete(Tc) &&
    Ds.decls_fin? &&
    wfe_type(n-1, Context([]), s, Tc) &&
    expansion(n-1, Context([]), s, y, Tc, Ds) && 
    wf_init(n-1, true, Context([]), s, lst2seq(decls_subst(y, tm_loc(loc), Ds.decls)), def_seq_sort(init));
  ensures exists n:nat, Ds:decls :: n>0 &&
    is_concrete(Tc) &&
    Ds.decls_fin? &&
    wfe_type(n-1, Context([]), s, Tc) &&
    expansion(n-1, Context([]), s, y, Tc, Ds) && 
    wf_init(n-1, true, Context([]), s, lst2seq(decls_subst(y, tm_loc(loc), Ds.decls)), def_seq_sort(init));
{
}

ghost method lemma_store_extends_well_typed(s: store, s': store, Tc: tp, init: seq<def>)
  requires store_well_typed(s);
  requires s'==Store(s.m+[P(Tc, init)]);
  requires store_well_typed1(s', |s.m|, fresh_from([]), Tc, init);
  ensures store_extends(s', s);
  ensures store_well_typed(s');
{
  parallel (l:nat | l < |s'.m|)
  ensures store_well_typed1(s', l, fresh_from([]), store_lookup_type(l, s'), store_lookup(l, s'));
  {
    if (l == |s.m|) {
    } else {
      assert l < |s.m|;
      var initl := store_lookup(l, s);
      var Tcl := store_lookup_type(l, s); 
      assert store_well_typed1(s, l, fresh_from([]), Tcl, initl);
      assert store_lookup(l, s') == initl;
      assert store_lookup_type(l, s') == Tcl;
      lemma_store_invariance_well_typed1(s, s', l, fresh_from([]), Tcl, initl);
    }
  }
}

predicate closed(t: tm)
{
  forall x: nat :: !tm_fn(x, t)
}

ghost method lemma_free_in_context_typing(x:nat, n: nat, ctx: context, s: store, t: tm, T: tp)
  requires tm_fn(x, t);
  requires typing(n, ctx, s, t, T);
  ensures context_lookup(ctx, x).Some?;
  requires typing(n, ctx, s, t, T);
{
  if (t.tm_var?) {
  } else if (t.tm_loc?) {
  } else if (t.tm_sel?) {
    assert membership(n-2, ctx, s, t.t, t.l, decl_tm(t.l, T));
    var To :| typing(n-3, ctx, s, t.t, To);
    lemma_free_in_context_typing(x, n-3, ctx, s, t.t, To);
  } else if (t.tm_msel?) {
    var S, T' :| method_membership(n-1, ctx, s, t.o, t.m, S, T) &&
    typing(n-1, ctx, s, t.a, T') &&
    subtype(n-1, ctx, s, T', S);
    assert membership(n-2, ctx, s, t.o, t.m, decl_mt(t.m, S, T));
    var To :| typing(n-3, ctx, s, t.o, To);
    assert tm_fn(x, t.o) || tm_fn(x, t.a);
    if (tm_fn(x, t.o)) {
      lemma_free_in_context_typing(x, n-3, ctx, s, t.o, To);
    }
    if (tm_fn(x, t.a)) {
      lemma_free_in_context_typing(x, n-1, ctx, s, t.a, T');
    }
  } else if (t.tm_new?) {
    if (t.y == x || tp_fn(x, t.Tc)) {
     assert tp_fn(x, t.Tc);
     assert wfe_type(n-1, ctx, s, t.Tc);
     lemma_free_in_context_wfe_type(x, n-1, ctx, s, t.Tc);
    } else {
      assert defs_fn(x, t.init) || tm_fn(x, t.t');
      if (tm_fn(x, t.t')) {
        var T' :| typing(n-1, context_extend(ctx, t.y, t.Tc), s, t.t', T');
        lemma_free_in_context_typing(x, n-1, context_extend(ctx, t.y, t.Tc), s, t.t', T');
      }
      if (defs_fn(x, t.init)) {
        assume context_lookup(ctx, x).Some?; // TODO (really!)
      }
    }
  } else {
  }
}
ghost method lemma_free_in_context_wfe_type(x: nat, n: nat, ctx: context, s: store, T: tp)
  requires tp_fn(x, T);
  requires wfe_type(n, ctx, s, T);
  ensures context_lookup(ctx, x).Some?;
  ensures wfe_type(n, ctx, s, T);
{
  assume context_lookup(ctx, x).Some?; // TODO (really!)
}
