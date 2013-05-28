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
  ensures fresh_from(ids)>0;
{
  max(ids, 0)+1
}

// ------
// Syntax
// ------

datatype tp = tp_sel(p: pt, L: nat, concrete: bool) | tp_rfn(base_tp: tp, self: nat, decls: list<decl>) | tp_and(and1: tp, and2: tp) | tp_or(or1: tp, or2: tp) | tp_top | tp_bot;
datatype pt = pt_var(x: nat) | pt_sel(p: pt, l: nat) |  pt_loc(loc: nat);
datatype bd = bd_new(Tc: tp, init: list<def>) | bd_snd(o: pt, m: nat, a: pt) | bd_exe(ov: nat, mv: nat, t': tm);
datatype tm = tm_path(p: pt) | tm_bind(y: nat, b: bd, t': tm);
datatype decl = decl_tp(L: nat, S: tp, U: tp, concrete: bool) | decl_tm(l: nat, T: tp) | decl_mt(m: nat, P: tp, R: tp);
datatype def = def_tm(l: nat, v: pt) | def_mt(m: nat, param: nat, body: tm);
datatype decls = decls_fin(decls: list<decl>) | decls_bot;

predicate is_concrete(T: tp)
{
  (T.tp_sel? && T.concrete) ||
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
  t.tm_path? && t.p.pt_loc?
}
predicate syn_value(t: tm)
{
  t.tm_path? && (t.p.pt_loc? || t.p.pt_var?)
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
function def_field_lookup(l: nat, defs: seq<def>): option<pt>
{
  if (exists i :: 0 <= i < |defs| && defs[i].def_tm? && defs[i].l==l)
  then (var i :| 0 <= i < |defs| && defs[i].def_tm? && defs[i].l==l; Some(defs[i].v))
  else None
}

// ### Size ###
function pt_size(p: pt): nat
  ensures p.pt_sel? ==> pt_size(p)==1+pt_size(p.p);
{
  match p
  case pt_var(x') => 1
  case pt_loc(loc) => 1
  case pt_sel(p1, l) => 1+pt_size(p1)
}
function bd_size(b: bd): nat
  ensures b.bd_new? ==> bd_size(b)==1+tp_size(b.Tc)+defs_size(b.init);
  ensures b.bd_new? ==> bd_size(b)>tp_size(b.Tc);
  ensures b.bd_new? ==> bd_size(b)>defs_size(b.init);
  ensures b.bd_snd? ==> bd_size(b)==1+pt_size(b.o)+pt_size(b.a);
  ensures b.bd_snd? ==> bd_size(b)>pt_size(b.o);
  ensures b.bd_snd? ==> bd_size(b)>pt_size(b.a);
  ensures b.bd_exe? ==> bd_size(b)==1+tm_size(b.t');
  ensures b.bd_exe? ==> bd_size(b)>tm_size(b.t');
{
  match b
  case bd_new(Tc, init) => 1+tp_size(Tc)+defs_size(init)
  case bd_snd(o, m, a) => 1+pt_size(o)+pt_size(a)
  case bd_exe(ov, mv, t') => 1+tm_size(t')
}
function tm_size(t: tm): nat
  ensures t.tm_path? ==> tm_size(t)==1+pt_size(t.p);
  ensures t.tm_path? ==> tm_size(t)>pt_size(t.p);
  ensures t.tm_bind? ==> tm_size(t)==1+bd_size(t.b)+tm_size(t.t');
  ensures t.tm_bind? ==> tm_size(t)>bd_size(t.b);
  ensures t.tm_bind? ==> tm_size(t)>tm_size(t.t');
{
  match t
  case tm_path(p) => 1+pt_size(p)
  case tm_bind(x, b, t') => 1+bd_size(b)+tm_size(t')
}
function tp_size(T: tp): nat
  ensures T.tp_sel? ==> tp_size(T)==1+pt_size(T.p);
  ensures T.tp_sel? ==> tp_size(T)>pt_size(T.p);
  ensures T.tp_rfn? ==> tp_size(T)==1+tp_size(T.base_tp)+decls_size(T.decls);
  ensures T.tp_rfn? ==> tp_size(T)>tp_size(T.base_tp);
  ensures T.tp_rfn? ==> tp_size(T)>decls_size(T.decls);
  ensures T.tp_and? ==> tp_size(T)==1+tp_size(T.and1)+tp_size(T.and2);
  ensures T.tp_and? ==> tp_size(T)>tp_size(T.and1);
  ensures T.tp_or? ==> tp_size(T)==1+tp_size(T.or1)+tp_size(T.or2);
  ensures T.tp_or? ==> tp_size(T)>tp_size(T.or1);
{
  match T
  case tp_sel(p, L, concrete) => 1+pt_size(p)
  case tp_rfn(base_tp, self, decls) => 1+tp_size(base_tp)+decls_size(decls)
  case tp_and(and1, and2) => 1+tp_size(and1)+tp_size(and2)
  case tp_or(or1, or2) => 1+tp_size(or1)+tp_size(or2)
  case tp_top => 1
  case tp_bot => 1
}
function def_size(d: def): nat
  ensures d.def_tm? ==> def_size(d)==1+pt_size(d.v);
  ensures d.def_tm? ==> def_size(d)>pt_size(d.v);
  ensures d.def_mt? ==> def_size(d)==1+tm_size(d.body);
  ensures d.def_mt? ==> def_size(d)>tm_size(d.body);
{
  match d
  case def_tm(l, v1) => 1+pt_size(v1)
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
function pt_subst(x: nat, v: pt, p: pt): pt
  decreases pt_size(p), p;
  ensures v.pt_var? ==> pt_size(p)==pt_size(pt_subst(x, v, p));
  ensures !pt_fn(x, p) ==> pt_subst(x, v, p)==p;
{
  match p
  case pt_var(x') => if x'==x then v else p
  case pt_sel(p1, l) => pt_sel(pt_subst(x, v, p1), l)
  case pt_loc(loc) => p
}
function bd_subst(x: nat, v: pt, b: bd): bd
  decreases bd_size(b), b;
  ensures v.pt_var? ==> bd_size(b)==bd_size(bd_subst(x, v, b));
  ensures !bd_fn(x, b) ==> bd_subst(x, v, b)==b;
{
  match b
  case bd_new(Tc, init) => bd_new(tp_subst(x, v, Tc), defs_subst(x, v, init))
  case bd_snd(o, m, a) => bd_snd(pt_subst(x, v, o), m, pt_subst(x, v, a))
  case bd_exe(ov, mv, t') => bd_exe(ov, mv, tm_subst(x, v, t'))
}
function tm_subst(x: nat, v: pt, t: tm): tm
  decreases tm_size(t), t;
  ensures v.pt_var? ==> tm_size(t)==tm_size(tm_subst(x, v, t));
  ensures !tm_fn(x, t) ==> tm_subst(x, v, t)==t;
{
  match t
  case tm_path(p) => tm_path(pt_subst(x, v, p))
  case tm_bind(y, b, t1) =>
    if !tm_fn(x, t) then t else
    if y==x then (if b.bd_new? then tm_bind(y, bd_new(tp_subst(x, v, b.Tc), b.init), t1) else tm_bind(y, bd_subst(x, v, b), t1)) else
    var y' := fresh_from([x]+pt_vars(v)+tm_vars(t));
    var b' := bd_subst(y, pt_var(y'), b);
    var t1' := tm_subst(y, pt_var(y'), t1);
    tm_bind(y', bd_subst(x, v, b'), tm_subst(x, v, t1'))
}
function tp_subst(x: nat, v: pt, T: tp): tp
  decreases tp_size(T), T;
  ensures v.pt_var? ==> tp_size(T)==tp_size(tp_subst(x, v, T));
  ensures !tp_fn(x, T) ==> tp_subst(x, v, T)==T;
{
  match T
  case tp_sel(p, L, concrete) => tp_sel(pt_subst(x, v, p), L, concrete)
  case tp_rfn(base_tp, self, decls) =>
    if !tp_fn(x, T) then T else
    if self==x then tp_rfn(tp_subst(x, v, base_tp), self, decls) else
    var self' := fresh_from([x]+pt_vars(v)+tp_vars(T));
    var decls' := decls_subst(self, pt_var(self'), decls);
    tp_rfn(tp_subst(x, v, base_tp), self', decls_subst(x, v, decls'))
  case tp_and(and1, and2) => tp_and(tp_subst(x, v, and1), tp_subst(x, v, and2))
  case tp_or(or1, or2) => tp_or(tp_subst(x, v, or1), tp_subst(x, v, or2))
  case tp_top => T
  case tp_bot => T
}
function def_subst(x: nat, v: pt, d: def): def
  decreases def_size(d), d;
  ensures v.pt_var? ==> def_size(d)==def_size(def_subst(x, v, d));
  ensures !def_fn(x, d) ==> def_subst(x, v, d)==d;
{
  match d
  case def_tm(l, v1) => def_tm(l, pt_subst(x, v, v1))
  case def_mt(m, param, body) =>
    if !def_fn(x, d) then d else
    if param==x then d else
    var param' := fresh_from([x]+pt_vars(v)+def_vars(d));
    var body' := tm_subst(param, pt_var(param'), body);
    def_mt(m, param', tm_subst(x, v, body'))
}
function decl_subst(x: nat, v: pt, d: decl): decl
  decreases decl_size(d), d;
  ensures v.pt_var? ==> decl_size(d)==decl_size(decl_subst(x, v, d));
  ensures !decl_fn(x, d) ==> decl_subst(x, v, d)==d;
{
  match d
  case decl_tp(L, S, U, concrete) => decl_tp(L, tp_subst(x, v, S), tp_subst(x, v, U), concrete)
  case decl_tm(l, T) => decl_tm(l, tp_subst(x, v, T))
  case decl_mt(m, P, R) => decl_mt(m, tp_subst(x, v, P), tp_subst(x, v, R))
}
function defs_subst(x: nat, v: pt, defs: list<def>): list<def>
  decreases defs_size(defs), defs;
  ensures v.pt_var? ==> defs_size(defs)==defs_size(defs_subst(x, v, defs));
  ensures !defs_fn(x, defs) ==> defs_subst(x, v, defs)==defs;
{
  match defs
  case Nil => Nil
  case Cons(head, tail) => Cons(def_subst(x, v, head), defs_subst(x, v, tail))
}
function decls_subst(x: nat, v: pt, decls: list<decl>): list<decl>
  decreases decls_size(decls), decls;
  ensures v.pt_var? ==> decls_size(decls)==decls_size(decls_subst(x, v, decls));
  ensures !decls_fn(x, decls) ==> decls_subst(x, v, decls)==decls;
{
  match decls
  case Nil => Nil
  case Cons(head, tail) => Cons(decl_subst(x, v, head), decls_subst(x, v, tail))
}

// ### Free variables ###
// fn(x, A) <==> x appears free in A

predicate pt_fn(x: nat, p: pt)
  ensures pt_fn(x, p) ==> x in pt_vars(p);
  decreases p;
{
  match p
  case pt_var(x') => x'==x
  case pt_sel(p1, l) => pt_fn(x, p1)
  case pt_loc(loc) => false
}

predicate bd_fn(x: nat, b: bd)
  ensures bd_fn(x, b) ==> x in bd_vars(b);
  decreases b;
{
  match b
  case bd_new(Tc, init) => tp_fn(x, Tc) || defs_fn(x, init)
  case bd_snd(o, m, a) => pt_fn(x, o) || pt_fn(x, a)
  case bd_exe(ov, mv, t') => tm_fn(x, t')
}

predicate tm_fn(x: nat, t: tm)
  ensures tm_fn(x, t) ==> x in tm_vars(t);
  decreases t;
{
  match t
  case tm_path(p) => pt_fn(x, p)
  case tm_bind(y, b, t') =>
    if (y==x) then (if b.bd_new? then tp_fn(x, b.Tc) else bd_fn(x, b)) else
    bd_fn(x, b) && tm_fn(x, t')
}

predicate tp_fn(x: nat, T: tp)
  ensures tp_fn(x, T) ==> x in tp_vars(T);
  decreases T;
{
  match T
  case tp_sel(p, L, concrete) => pt_fn(x, p)
  case tp_rfn(base_tp, self, decls) => tp_fn(x, base_tp) || (self!=x && decls_fn(x, decls))
  case tp_and(and1, and2) => tp_fn(x, and1) || tp_fn(x, and2)
  case tp_or(or1, or2) => tp_fn(x, or1) || tp_fn(x, or2)
  case tp_top => false
  case tp_bot => false
}
predicate def_fn(x: nat, d: def)
  ensures def_fn(x, d) ==> x in def_vars(d);
  decreases d;
{
  match d
  case def_tm(l, v1) => pt_fn(x, v1)
  case def_mt(m, param, body) => param!=x && tm_fn(x, body)
}
predicate decl_fn(x: nat, d: decl)
  ensures decl_fn(x, d) ==> x in decl_vars(d);
  decreases d;
{
  match d
  case decl_tp(L, S, U, concrete) => tp_fn(x, S) || tp_fn(x, U)
  case decl_tm(l, T) => tp_fn(x, T)
  case decl_mt(m, P, R) => tp_fn(x, P) || tp_fn(x, R)
}
predicate defs_fn(x: nat, defs: list<def>)
  ensures defs_fn(x, defs) ==> x in defs_vars(defs);
  decreases defs;
{
  defs.Cons? && (def_fn(x, defs.head) || defs_fn(x, defs.tail))
}
predicate decls_fn(x: nat, decls: list<decl>)
  ensures decls_fn(x, decls) ==> x in decls_vars(decls);
  decreases decls;
{
  decls.Cons? && (decl_fn(x, decls.head) || decls_fn(x, decls.tail))
}

// ### Variables ###

function pt_vars(p: pt): seq<int>
  ensures forall x :: x in pt_vars(p) ==> x>=0;
{
  match p
  case pt_var(x') => [x']
  case pt_sel(p1, l) => pt_vars(p1)
  case pt_loc(loc) => []
}

function bd_vars(b: bd): seq<int>
  ensures forall x :: x in bd_vars(b) ==> x>=0;
{
  match b
  case bd_new(Tc, init) => tp_vars(Tc)+defs_vars(init)
  case bd_snd(o, m, a) => pt_vars(o)+pt_vars(a)
  case bd_exe(ov, mv, t') => tm_vars(t')
}

function tm_vars(t: tm): seq<int>
  ensures forall x :: x in tm_vars(t) ==> x>=0;
{
  match t
  case tm_path(p) => pt_vars(p)
  case tm_bind(y, b, t') => [y]+bd_vars(b)+tm_vars(t')
}

function tp_vars(T: tp): seq<int>
  ensures forall x :: x in tp_vars(T) ==> x>=0;
{
  match T
  case tp_sel(p, L, concrete) => pt_vars(p)
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
  case def_tm(l, v1) => pt_vars(v1)
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
  ensures defs.Cons? ==> defs_vars(defs)==def_vars(defs.head)+defs_vars(defs.tail);
{
  match defs
  case Nil => []
  case Cons(head, tail) => def_vars(head)+defs_vars(tail)
}
function decls_vars(decls: list<decl>): seq<int>
  ensures forall x :: x in decls_vars(decls) ==> x>=0;
  ensures decls.Cons? ==> decls_vars(decls)==decl_vars(decls.head)+decls_vars(decls.tail);
{
  match decls
  case Nil => []
  case Cons(head, tail) => decl_vars(head)+decls_vars(tail)
}

// ### Reduction ###
function pt_step(p: pt, s: store): option<pt>
{
  /* sel */
  if (p.pt_sel? && p.p.pt_loc? && p.p.loc < |s.m| &&
      def_field_lookup(p.l, store_lookup(p.p.loc, s)).Some?)
  then Some(def_field_lookup(p.l, store_lookup(p.p.loc, s)).get)
  /* sel-c */
  else if (p.pt_sel? && pt_step(p.p, s).Some?)
  then Some(pt_sel(pt_step(p.p, s).get, p.l))
  else None
}

function step(t: tm, s: store): option<pair<tm, store>>
{
  if (t.tm_path? && pt_step(t.p, s).Some?)
  then Some(P(tm_path(pt_step(t.p, s).get), s))
  /* new */
  else if (t.tm_bind? && t.b.bd_new?)
  then Some(P(tm_subst(t.y, pt_loc(|s.m|), t.t'),
              Store(s.m+[P(t.b.Tc, lst2seq(defs_subst(t.y, pt_loc(|s.m|), t.b.init)))])))
  /* snd */
  else if (t.tm_bind? && t.b.bd_snd? && t.b.o.pt_loc? && value(tm_path(t.b.a)) && t.b.o.loc < |s.m| &&
     def_method_lookup(t.b.m, store_lookup(t.b.o.loc, s)).Some?)
  then Some(P(tm_bind(t.y,
                      bd_exe(t.b.o.loc, t.b.m,
                             tm_subst(def_method_lookup(t.b.m, store_lookup(t.b.o.loc, s)).get.fst,
                                      t.b.a,
                                      def_method_lookup(t.b.m, store_lookup(t.b.o.loc, s)).get.snd)),
                      t.t'),
              s))
  /* snd-c-obj */
  else if (t.tm_bind? && t.b.bd_snd? && pt_step(t.b.o, s).Some?)
  then Some(P(tm_bind(t.y, bd_snd(pt_step(t.b.o, s).get, t.b.m, t.b.a), t.t'), s))
  /* snd-c-arg */
  else if (t.tm_bind? && t.b.bd_snd? && value(tm_path(t.b.o)) && pt_step(t.b.a, s).Some?)
  then Some(P(tm_bind(t.y, bd_snd(t.b.o, t.b.m, pt_step(t.b.a, s).get), t.t'), s))
  /* exe */
  else if (t.tm_bind? && t.b.bd_exe? && value(t.b.t'))
  then Some(P(tm_subst(t.y, t.b.t'.p, t.t'), s))
  /* exe-c */
  else if (t.tm_bind? && t.b.bd_exe? && step(t.b.t', s).Some?)
  then Some(P(tm_bind(t.y, bd_exe(t.b.ov, t.b.mv, step(t.b.t', s).get.fst), t.t'), step(t.b.t', s).get.snd))
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
  requires o.tm_path? && o'.tm_path?;
  requires mstep(o, s, o', s', oi);
  ensures mstep(tm_path(pt_sel(o.p, l)), s, tm_path(pt_sel(o'.p, l)), s', oi);
  decreases oi;
{
  if (oi>0) {
    lemma_mstep_sel(step(o, s).get.fst, l, o', step(o, s).get.snd, s', oi-1);
  }
}

ghost method lemma_sel_irred__o_mstep_irred(o: tm, l: nat, t': tm, s: store, s': store, i: nat) returns (o': tm, so': store, oi: nat)
  requires o.tm_path?;
  requires mstep(tm_path(pt_sel(o.p, l)), s, t', s', i);
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
    lemma_mstep_trans'(tm_path(pt_sel(o.p, l)), s, tm_path(pt_sel(step(o, s).get.fst.p, l)), step(o, s).get.snd, t', s', 1, i);
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
  requires context_lookup(ctx, x).None?;
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
function dom(ctx: context): seq<int>
  ensures forall x:nat :: x !in dom(ctx) ==> context_lookup(ctx, x).None?;
  ensures forall x:nat :: x in dom(ctx) ==> context_lookup(ctx, x).Some?;
  decreases |ctx.m|;
{
  if (ctx.m==[]) then [] else [ctx.m[0].fst]+dom(Context(ctx.m[1..]))
}
function fresh_in_context(ctx: context): nat
  ensures context_lookup(ctx, fresh_in_context(ctx)).None?;
{
  fresh_from(dom(ctx))
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

predicate typing(n: nat, ctx: context, s: store, p: pt, T: tp)
  decreases n;
{
  match p
  case pt_var(x) => context_lookup(ctx, x)==Some(T)
  case pt_sel(p1, l) =>
    n>0 && field_membership(n-1, ctx, s, p1, l, T)
  case pt_loc(loc) => loc < |s.m| && store_lookup_type(loc, s)==T
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
  case tp_rfn(T', z_, Ds_) =>
    var z:= fresh_in_context(ctx);
    var Ds := decls_subst(z_, pt_var(z), Ds_);
    n>0 && wf_type(n-1, ctx, s, T') && wf_decls(n-1, context_extend(ctx, z, T), s, lst2seq(Ds))
  case tp_sel(p, L, concrete) =>
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
predicate membership(n: nat, ctx: context, s: store, p: pt, l: nat, d: decl)
  decreases n;
{
  var z:nat := fresh_in_context(ctx);
  decl_label(d)==l &&
  n>0 && exists T :: typing(n-1, ctx, s, p, T) &&
  exists Ds ::
  expansion(n-1, ctx, s, z, T, Ds) &&
  ((Ds.decls_fin? &&
    exists d' :: d' in lst2seq(Ds.decls) && d==decl_subst(z, p, d')) ||
   (Ds.decls_bot? && decl_bot(d)))
}
predicate field_membership(n: nat, ctx: context, s: store, p: pt, l: nat, T: tp)
  decreases n;
{
  n>0 && membership(n-1, ctx, s, p, l, decl_tm(l, T))
}
predicate method_membership(n: nat, ctx: context, s: store, p: pt, m: nat, P: tp, R: tp)
  decreases n;
{
  n>0 && exists d :: membership(n-1, ctx, s, p, m, d) &&
  d.decl_mt? && d.m==m && d.P==P && d.R==R
}
predicate type_membership(n: nat, ctx: context, s: store, p: pt, L: nat, concrete: bool, S: tp, U: tp)
  decreases n;
{
  n>0 && exists d :: membership(n-1, ctx, s, p, L, d) &&
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
predicate expansion_iter(n: nat, m: seq<tp>, ctx: context, s: store, z: nat, T: tp, Ds: decls)
  decreases n;
{
  match T
  case tp_rfn(T', z', Ds') =>
    n>0 &&
    exists DsT' :: expansion_iter(n-1, m, ctx, s, z, T', DsT') &&
    exists rfn_decls :: rfn_decls==decl_seq_sort(lst2seq(decls_subst(z', pt_var(z), Ds'))) &&
    Ds==decls_and(decls_fin(seq2lst(rfn_decls)), DsT')
  case tp_sel(p, L, concrete) =>
    (T in m && Ds==decls_fin(Nil)) || 
    (n>0 && T !in m && exists S, U :: type_membership(n-1, ctx, s, p, L, concrete, S, U) &&
    expansion_iter(n-1, [T]+m, ctx, s, z, U, Ds))
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
predicate path_red(ctx: context, s: store, p1: pt, p2: pt)
{
  (p1.pt_sel? && p1.p.pt_loc? && p2.pt_loc? && p1.p.loc < |s.m| &&
   def_field_lookup(p1.l, store_lookup(p1.p.loc, s)).Some? &&
   p2==def_field_lookup(p1.l, store_lookup(p1.p.loc, s)).get) ||
  (p1.pt_sel? && p2.pt_sel? && p1.l==p2.l && path_red(ctx, s, p1.p, p2.p))
}

predicate subtype(n: nat, ctx: context, s: store, S: tp, T: tp)
  decreases n;
{
  var self := fresh_in_context(ctx);
  n>0 && (
  /* refl */    (S==T && wfe_type(n-1, ctx, s, T)) ||
  /* <:-top */  (T.tp_top? && wfe_type(n-1, ctx, s, S)) ||
  /* bot-<: */  (S.tp_bot? && wfe_type(n-1, ctx, s, T)) ||
  /* <:-rfn */  (T.tp_rfn? && wfe_type(n-1, ctx, s, T) && subtype(n-1, ctx, s, S, T.base_tp) &&
                 exists Ds' :: expansion(n-1, ctx, s, self, S, Ds') &&
                 exists rfn_decls :: rfn_decls==decl_seq_sort(lst2seq(decls_subst(T.self, pt_var(self), T.decls))) &&
                 decls_sub(n-1, context_extend(ctx, self, S), s, decls_fin(seq2lst(rfn_decls)), Ds')) ||
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

predicate typing'(ctx: context, s: store, p: pt, T: tp)
{
  exists n:nat :: typing(n, ctx, s, p, T)
}
predicate wfe_type'(ctx: context, s: store, T: tp)
{
  exists n:nat :: wfe_type(n, ctx, s, T)
}
predicate membership'(ctx: context, s: store, t: pt, l: nat, d: decl)
{
  exists n:nat :: membership(n, ctx, s, t, l, d)
}
predicate field_membership'(ctx: context, s: store, t: pt, l: nat, T: tp)
{
  exists n:nat :: field_membership(n, ctx, s, t, l, T)
}
predicate method_membership'(ctx: context, s: store, t: pt, m: nat, P: tp, R: tp)
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
function typing_n(ctx: context, s: store, t: pt, T: tp): nat
  requires typing'(ctx, s, t, T);
  ensures typing(typing_n(ctx, s, t, T), ctx, s, t, T);
{
  var n:nat :| typing(n, ctx, s, t, T); n
}
function wfe_type_n(ctx: context, s: store, T: tp): nat
  requires wfe_type'(ctx, s, T);
  ensures wfe_type(wfe_type_n(ctx, s, T), ctx, s, T);
{
  var n:nat :| wfe_type(n, ctx, s, T); n
}
function field_membership_n(ctx: context, s: store, t: pt, l: nat, T: tp): nat
  requires field_membership'(ctx, s, t, l, T);
  ensures field_membership(field_membership_n(ctx, s, t, l, T), ctx, s, t, l, T);
{
  var n:nat :| field_membership(n, ctx, s, t, l, T); n
}
function method_membership_n(ctx: context, s: store, t: pt, m: nat, P: tp, R: tp): nat
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

ghost method lemma_typing_monotonic_plus(m: nat, n: nat, ctx: context, s: store, t: pt, T: tp)
  requires m<=n;
  requires typing(m, ctx, s, t, T);
  ensures typing(n, ctx, s, t, T);
  decreases n-m;
{
  if (n==m) {}
  else {
    lemma_typing_monotonic(m, ctx, s, t, T);
    lemma_typing_monotonic_plus(m+1, n, ctx, s, t, T);
  }
}
ghost method lemma_typing_monotonic(n: nat, ctx: context, s: store, t: pt, T: tp)
  requires typing(n, ctx, s, t, T);
  ensures typing(n+1, ctx, s, t, T);
{
  if (t.pt_var?) {
    assert typing(n+1, ctx, s, t, T);
  } else if (t.pt_sel?) {
    if (n>0) {
      lemma_field_membership_monotonic(n-1, ctx, s, t.p, t.l, T);
    }
  }
}
ghost method lemma_wfe_type_monotonic(n: nat, ctx: context, s: store, T: tp)
  requires wfe_type(n, ctx, s, T);
  ensures wfe_type(n+1, ctx, s, T);
{
  assume wfe_type(n+1, ctx, s, T); // TODO
}
ghost method lemma_field_membership_monotonic(n: nat, ctx: context, s: store, t: pt, l: nat, T: tp)
  requires field_membership(n, ctx, s, t, l, T);
  ensures field_membership(n+1, ctx, s, t, l, T);
{
  assume field_membership(n+1, ctx, s, t, l, T); // TODO
}
ghost method lemma_method_membership_monotonic(n: nat, ctx: context, s: store, t: pt, m: nat, P: tp, R: tp)
  requires method_membership(n, ctx, s, t, m, P, R);
  ensures method_membership(n+1, ctx, s, t, m, P, R);
{
  assume method_membership(n+1, ctx, s, t, m, P, R); // TODO
}
ghost method lemma_method_membership_monotonic_plus(m: nat, n: nat, ctx: context, s: store, t: pt, md: nat, P: tp, R: tp)
  requires m<=n;
  requires method_membership(m, ctx, s, t, md, P, R);
  ensures method_membership(n, ctx, s, t, md, P, R);
  decreases n-m;
{
  if (n==m) {}
  else {
    lemma_method_membership_monotonic(m, ctx, s, t, md, P, R);
    lemma_method_membership_monotonic_plus(m+1, n, ctx, s, t, md, P, R);
  }
}
ghost method lemma_expansion_monotonic_plus(m: nat, n: nat, ctx: context, s: store, z: nat, T: tp, Ds: decls)
  requires m <= n;
  requires expansion(m, ctx, s, z, T, Ds);
  ensures expansion(n, ctx, s, z, T, Ds);
  decreases n-m;
{
 if (n==m) {}
  else {
    lemma_expansion_monotonic(m, ctx, s, z, T, Ds);
    lemma_expansion_monotonic_plus(m+1, n, ctx, s, z, T, Ds);
  }
}
ghost method lemma_expansion_monotonic(n: nat, ctx: context, s: store, z: nat, T: tp, Ds: decls)
  requires expansion(n, ctx, s, z, T, Ds);
  ensures expansion(n+1, ctx, s, z, T, Ds);
{
  assume expansion(n+1, ctx, s, z, T, Ds); // TODO
}
ghost method lemma_subtype_monotonic_plus(m: nat, n: nat, ctx: context, s: store, S: tp, T: tp)
  requires m<=n;
  requires subtype(m, ctx, s, S, T);
  ensures subtype(n, ctx, s, S, T);
  decreases n-m;
{
  if (n==m) {}
  else {
    lemma_subtype_monotonic(m, ctx, s, S, T);
    lemma_subtype_monotonic_plus(m+1, n, ctx, s, S, T);
  }
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
predicate tm_closed(t: tm)
{
  forall x: nat :: !tm_fn(x, t)
}
predicate tp_closed(T: tp)
{
  forall x: nat :: !tp_fn(x, T)
}
predicate def_closed(d: def)
{
  forall x:nat :: !def_fn(x, d)
}
predicate store_extends<A>(s': store, s: store)
{
  |s.m|<=|s'.m| && forall l:nat :: l < |s.m| ==> s.m[l]==s'.m[l]
}
ghost method lemma_decl_bot__subst_idem(x: nat, s: pt, d: decl)
  requires decl_bot(d);
  ensures decl_bot(decl_subst(x, s, d));
  ensures decl_eq(d, decl_subst(x, s, d));
{
}

// Typing statements

predicate typeok(n: nat, ctx: context, s: store, t: tm, T: tp)
  decreases n;
{
  match t
  case tm_path(p) =>
    n>0 && exists Tp :: typing(n-1, ctx, s, p, Tp) && subtype(n-1, ctx, s, Tp, T)
  case tm_bind(y_, b, t'_) =>
    (match b
      case bd_new(Tc, init_) =>
        var y := fresh_from(dom(ctx)+tm_vars(t)+tp_vars(T));
        var t' := tm_subst(y_, pt_var(y), t'_);
        var init := defs_subst(y_, pt_var(y), init_);
        n>0 && is_concrete(Tc) &&
        wfe_type(n-1, ctx, s, Tc) &&
        exists Ds:decls :: Ds.decls_fin? &&
        expansion(n-1, ctx, s, y, Tc, Ds) &&
        wf_init(n-1, false, context_extend(ctx, y, Tc), s, lst2seq(Ds.decls), lst2seq(init)) &&
        typeok(n-1, context_extend(ctx, y, Tc), s, t', T)
      case bd_snd(o, m, a) =>
        var y := fresh_from(dom(ctx)+tm_vars(t)+tp_vars(T));
        var t' := tm_subst(y_, pt_var(y), t'_);
        n>0 && exists P, R :: method_membership(n-1, ctx, s, o, m, P, R) &&
        typeok(n-1, ctx, s, tm_path(a), P) &&
        typeok(n-1, context_extend(ctx, y, R), s, t', T)
      case bd_exe(ov, mv, tb) =>
        var y := fresh_from(dom(ctx)+tm_vars(t)+tp_vars(T));
        var t' := tm_subst(y_, pt_var(y), t'_);
        n>0 && exists P, R :: method_membership(n-1, ctx, s, pt_loc(ov), mv, P, R) &&
        typeok(n-1, ctx, s, tb, R) &&
        typeok(n-1, context_extend(ctx, y, R), s, t', T)
    )
}
predicate wf_init(n: nat, already_in_store: bool, ctx: context, s: store, decls: seq<decl>, defs: seq<def>)
  decreases n;
{
  var p:nat := fresh_in_context(ctx);
  n>0 && forall d :: d in decls ==> (
  if (d.decl_tp?) then subtype(n-1, ctx, s, d.S, d.U)
  else if (d.decl_tm?) then exists def :: def in defs && def.def_tm? && def.l==d.l && (if already_in_store then value(tm_path(def.v)) else syn_value(tm_path(def.v))) && typeok(n-1, ctx, s, tm_path(def.v), d.T)
  else if (d.decl_mt?) then exists def :: def in defs && def.def_mt? && def.m==d.m && typeok(n-1, context_extend(ctx, p, d.P), s, tm_subst(def.param, pt_var(p), def.body), d.R)
  else false)
}

ghost method lemma_typeok_monotonic_plus(m: nat, n: nat, ctx: context, s: store, t: tm,  T: tp)
  requires m<=n;
  requires typeok(m, ctx, s, t, T);
  ensures typeok(n, ctx, s, t, T);
  decreases n-m;
{
  if (n==m) {}
  else {
    lemma_typeok_monotonic(m, ctx, s, t, T);
    lemma_typeok_monotonic_plus(m+1, n, ctx, s, t, T);
  }
}
ghost method lemma_typeok_monotonic(n: nat, ctx: context, s: store, t: tm, T: tp)
  requires typeok(n, ctx, s, t, T);
  ensures typeok(n+1, ctx, s, t, T);
{
  // TODO
  assume typeok(n+1, ctx, s, t, T);
}

predicate store_wf1(n: nat, s: store, loc: nat, y: nat, Tc: tp, init: seq<def>)
{
  n>0 &&
  is_concrete(Tc) &&
  exists Ds:decls :: Ds.decls_fin? &&
  wfe_type(n-1, Context([]), s, Tc) &&
  expansion(n-1, Context([]), s, y, Tc, Ds) && 
  wf_init(n-1, true, Context([]), s, lst2seq(decls_subst(y, pt_loc(loc), Ds.decls)), init) &&
  tp_closed(Tc) &&
  forall d :: d in init ==> def_closed(d)
}
predicate store_wf(n: nat, s: store)
{
  forall l:nat :: l < |s.m| ==> store_wf1(n, s, l, fresh_from([]), store_lookup_type(l, s), store_lookup(l, s))
}

ghost method lemma_store_wf_field_ok(n: nat, s: store, loc: nat, l: nat, nt: nat, T: tp) returns (locl: nat, T': tp, nt': nat)
  requires store_wf(n, s);
  ensures pt_step(pt_sel(pt_loc(loc), l), s) == Some(pt_loc(locl));
  requires typing(nt, Context([]), s, pt_sel(pt_loc(loc), l), T);
  ensures typing(nt', Context([]), s, pt_loc(locl), T') && subtype(nt', Context([]), s, T', T);
{
  // TODO!
  assume exists locl:nat :: pt_step(pt_sel(pt_loc(loc), l), s) == Some(pt_loc(locl));
  var locl_:nat :| pt_step(pt_sel(pt_loc(loc), l), s) == Some(pt_loc(locl_));
  locl := locl_;

  // TODO!
  assume exists T', nt':nat :: typing(nt', Context([]), s, pt_loc(locl), T') && subtype(nt', Context([]), s, T', T);
  var T'_, nt'_:nat :| typing(nt'_, Context([]), s, pt_loc(locl), T'_) && subtype(nt'_, Context([]), s, T'_, T);
  T' := T'_;
  nt' := nt'_;
}

ghost method lemma_store_wf_method_ok(n: nat, s: store, loc: nat, m: nat, nt: nat, P_: tp, R: tp) returns (x: nat, body: tm, nbody: nat)
  requires store_wf(n, s);
  requires loc < |s.m|;
  requires method_membership(nt, Context([]), s, pt_loc(loc), m, P_, R);
  ensures def_method_lookup(m, store_lookup(loc, s)) == Some(P(x, body));
  ensures typeok(nbody, context_extend(Context([]), x, P_), s, body, R);
  ensures !tp_fn(x, P_) && !tp_fn(x, R);
{
  // TODO: not needed for preservation, but will be needed for progress
  assume def_method_lookup(m, store_lookup(loc, s)).Some?;
  x := def_method_lookup(m, store_lookup(loc, s)).get.fst;
  body := def_method_lookup(m, store_lookup(loc, s)).get.snd;
  // TODO
  assume exists nbody:nat :: typeok(nbody, context_extend(Context([]), x, P_), s, body, R);
  var nbody_:nat :| typeok(nbody_, context_extend(Context([]), x, P_), s, body, R);
  nbody := nbody_;
  // TODO: might need to change wf...
  assume !tp_fn(x, P_) && !tp_fn(x, R);
}

ghost method theorem_subtype_transitive(ctx: context, s: store, n12: nat, n23: nat, T1: tp, T2: tp, T3: tp) returns (n13: nat)
  requires subtype(n12, ctx, s, T1, T2);
  requires subtype(n23, ctx, s, T2, T3);
  ensures subtype(n13, ctx, s, T1, T3);
{
  // TODO!
  assume exists n13:nat :: subtype(n13, ctx, s, T1, T3);
  var n13_:nat :| subtype(n13_, ctx, s, T1, T3);
  n13 := n13_;
}

ghost method lemma_subtype_inversion(ctx: context, s: store, np: nat, p: pt, Tp: tp, np': nat, p': pt, Tp': tp, ns: nat, nm: nat, l: nat, d: decl) returns (d': decl, nm': nat)
  requires pt_step(p, s).Some? && pt_step(p, s).get==p';
  requires typing(np, ctx, s, p, Tp);
  requires typing(np', ctx, s, p', Tp');
  requires subtype(ns, ctx, s, Tp', Tp);
  requires membership(nm, ctx, s, p, l, d);
  ensures decl_eq(d', d) && membership(nm', ctx, s, p', l, d') && decl_sub(nm', ctx, s, d', d);
{
  // TODO!
  assume exists d', nm':nat :: decl_eq(d', d) && membership(nm', ctx, s, p', l, d') && decl_sub(nm', ctx, s, d', d);
  var d'_, nm'_:nat :| decl_eq(d'_, d) && membership(nm'_, ctx, s, p', l, d'_) && decl_sub(nm'_, ctx, s, d'_, d);
  d' := d'_;
  nm' := nm'_;
}

ghost method lemma_subtype_inversion_field(ctx: context, s: store, np: nat, p: pt, Tp: tp, np': nat, p': pt, Tp': tp, ns: nat, nm: nat, l: nat, T: tp) returns (T': tp, nm': nat)
  requires pt_step(p, s).Some? && pt_step(p, s).get==p';
  requires typing(np, ctx, s, p, Tp);
  requires typing(np', ctx, s, p', Tp');
  requires subtype(ns, ctx, s, Tp', Tp);
  requires field_membership(nm, ctx, s, p, l, T);
  ensures field_membership(nm', ctx, s, p', l, T') && subtype(nm', ctx, s, T', T);
{
  assert membership(nm-1, ctx, s, p, l, decl_tm(l, T));
  var d', nd' := lemma_subtype_inversion(ctx, s, np, p, Tp, np', p', Tp', ns, nm-1, l, decl_tm(l, T));
  T' := d'.T;
  nm' := nd'+1;
  lemma_subtype_monotonic_plus(nd'-1, nm', ctx, s, T', T);
}

ghost method lemma_subtype_inversion_method(ctx: context, s: store, np: nat, p: pt, Tp: tp, np': nat, p': pt, Tp': tp, ns: nat, nm: nat, m: nat, P: tp, R: tp) returns (P': tp, R': tp, nm': nat)
  requires pt_step(p, s).Some? && pt_step(p, s).get==p';
  requires typing(np, ctx, s, p, Tp);
  requires typing(np', ctx, s, p', Tp');
  requires subtype(ns, ctx, s, Tp', Tp);
  requires method_membership(nm, ctx, s, p, m, P, R);
  ensures method_membership(nm', ctx, s, p', m, P', R') && subtype(nm', ctx, s, P, P') && subtype(nm', ctx, s, R', R);
{
  assert membership(nm-1, ctx, s, p, m, decl_mt(m, P, R));
  var d', nd' := lemma_subtype_inversion(ctx, s, np, p, Tp, np', p', Tp', ns, nm-1, m, decl_mt(m, P, R));
  P' := d'.P;
  R' := d'.R;
  nm' := nd'+1;
  lemma_subtype_monotonic_plus(nd'-1, nm', ctx, s, P, P');
  lemma_subtype_monotonic_plus(nd'-1, nm', ctx, s, R', R);
}

ghost method theorem_pt_preservation(s: store, ns: nat, p: pt, T: tp, np: nat, p': pt) returns (T': tp, np': nat)
  requires store_wf(ns, s);
  requires typing(np, Context([]), s, p, T);
  requires pt_step(p, s) == Some(p');
  ensures typing(np', Context([]), s, p', T') && subtype(np', Context([]), s, T', T);
{
  var p1 := p.p;
  var l := p.l;    
  if (pt_step(p1, s).Some?) {
    var p1' := pt_step(p1, s).get;
    assert p' == pt_sel(p1', l);
    assert field_membership(np-1, Context([]), s, p1, l, T);
    assert membership(np-2, Context([]), s, p1, l, decl_tm(l, T));
    assert exists Tp1 :: typing(np-3, Context([]), s, p1, Tp1);
    var Tp1 :| typing(np-3, Context([]), s, p1, Tp1);
    var Tp1', np1' := theorem_pt_preservation(s, ns, p1, Tp1, np-3, p1');
    assert typing(np1', Context([]), s, p1', Tp1') && subtype(np1', Context([]), s, Tp1', Tp1);
    var T'_, np'_ := lemma_subtype_inversion_field(Context([]), s, np-3, p1, Tp1, np1', p1', Tp1', np1', np-1, l, T);
    T' := T'_;
    np' := np'_+1;
    lemma_subtype_monotonic_plus(np'_, np', Context([]), s, T', T);
  } else {
    assert p1.pt_loc?;
    var locl, T'_, np'_ := lemma_store_wf_field_ok(ns, s, p1.loc, l, np, T);
    assert p'.loc == locl;
    T' := T'_;
    np' := np'_;
  }
}

ghost method lemma_subst(s: store, ns: nat, t: tm, T: tp, nt: nat, y: nat, S: tp, v: tm, nv: nat) returns (nt': nat)
  requires store_wf(ns, s);
  requires !tp_fn(y, T);
  requires typeok(nt, context_extend(Context([]), y, S), s, t, T);
  requires value(v);
  requires typeok(nv, Context([]), s, v, S);
  ensures typeok(nt', Context([]), s, tm_subst(y, v.p, t), T);
{
  // TODO!
  assume exists nt':nat :: typeok(nt', Context([]), s, tm_subst(y, v.p, t), T);
  var nt'_:nat :| typeok(nt'_, Context([]), s, tm_subst(y, v.p, t), T);
  nt' := nt'_;
}

ghost method lemma_subst_in_context(s: store, ns: nat, t: tm, T: tp, nt: nat, y: nat, S: tp, S': tp, nsub: nat) returns (nt': nat)
  requires store_wf(ns, s);
  requires !tp_fn(y, T);
  requires typeok(nt, context_extend(Context([]), y, S), s, t, T);
  requires subtype(nsub, Context([]), s, S', S);
  ensures typeok(nt', context_extend(Context([]), y, S'), s, t, T);
{
  // TODO!
  assume exists nt':nat :: typeok(nt', context_extend(Context([]), y, S'), s, t, T);
  var nt'_:nat :| typeok(nt'_, context_extend(Context([]), y, S'), s, t, T);
  nt' := nt'_;
}

ghost method lemma_store_invariance_typeok(ctx: context, s: store, s': store, ns': nat, t: tm, T: tp, nt: nat) returns (nt': nat)
  requires store_extends(s', s);
  requires store_wf(ns', s');
  requires typeok(nt, ctx, s, t, T);
  ensures typeok(nt', ctx, s', t, T);
{
  // TODO!
  assume exists nt':nat :: typeok(nt', ctx, s', t, T);
  var nt'_:nat :| typeok(nt'_, ctx, s', t, T);
  nt' := nt'_;
}

ghost method lemma_store_invariance_method_membership(ctx: context, s: store, s': store, ns': nat, o: pt, m: nat, P: tp, R: tp, nm: nat) returns (nm': nat)
  requires store_extends(s', s);
  requires store_wf(ns', s');
  requires method_membership(nm, ctx, s, o, m, P, R);
  ensures method_membership(nm', ctx, s', o, m, P, R);
{
  // TODO!
  assume exists nm':nat :: method_membership(nm', ctx, s', o, m, P, R);
  var nm'_:nat :| method_membership(nm'_, ctx, s', o, m, P, R);
  nm' := nm'_;
}
ghost method lemma_store_invariance_wfe_type(ctx: context, s: store, s': store, ns': nat, T: tp, nT: nat) returns (nT': nat)
  requires store_extends(s', s);
  requires store_wf(ns', s');
  requires wfe_type(nT, ctx, s, T);
  ensures wfe_type(nT', ctx, s', T);
{
  // TODO!
  assume exists nT':nat :: wfe_type(nT', ctx, s', T);
  var nT'_:nat :| wfe_type(nT'_, ctx, s', T);
  nT' := nT'_;
}

ghost method lemma_store_wf_new(s: store, ns: nat, s': store, t: tm, T: tp, nt: nat, t': tm) returns (ns': nat)
  requires store_wf(ns, s);
  requires t.tm_bind? && t.b.bd_new?;
  requires step(t, s) == Some(P(t', s'));
  ensures store_wf(ns', s');
  ensures store_extends(s', s);
{
  // TODO!
  assume store_extends(s', s);
  assume exists ns':nat :: store_wf(ns', s');
  var ns'_:nat :| store_wf(ns'_, s');
  ns' := ns'_;
}

ghost method lemma_fresh_subst_typeok(ctx: context, s: store, t: tm, T: tp, v: pt, y: nat, t'_: tm, nt: nat)
  requires t.tm_bind?;
  requires y==fresh_from(dom(ctx)+tm_vars(t)+tp_vars(T));
  requires t'_==tm_subst(t.y, pt_var(y), t.t');
  requires typeok(nt, ctx, s, tm_subst(y, v, t'_), T);
  ensures typeok(nt, ctx, s, tm_subst(t.y, v, t.t'), T);
{
  // TODO
  assume typeok(nt, ctx, s, tm_subst(t.y, v, t.t'), T);
}

ghost method theorem_preservation_path(s: store, ns: nat, t: tm, T: tp, nt: nat, t': tm, s': store) returns (ns': nat, nt': nat)
  requires t.tm_path?;
  requires store_wf(ns, s);
  requires typeok(nt, Context([]), s, t, T);
  requires step(t, s) == Some(P(t', s'));
  ensures store_extends(s', s);
  ensures store_wf(ns', s');
  ensures typeok(nt', Context([]), s', t', T);
{
  var Tp :| typing(nt-1, Context([]), s, t.p, Tp) && subtype(nt-1, Context([]), s, Tp, T);
  var Tp'_, np'_ := theorem_pt_preservation(s, ns, t.p, Tp, nt-1, t'.p);
  var nt'_ := theorem_subtype_transitive(Context([]), s, np'_, nt-1, Tp'_, Tp, T);
  nt' := nt'_+np'_+1;
  lemma_typing_monotonic_plus(np'_, nt'-1, Context([]), s, t'.p, Tp'_);
  lemma_subtype_monotonic_plus(nt'_, nt'-1, Context([]), s, Tp'_, T);
  ns' := ns;
}

ghost method theorem_preservation_new(s: store, ns: nat, t: tm, T: tp, nt: nat, t': tm, s': store) returns (ns': nat, nt': nat)
  requires t.tm_bind? && t.b.bd_new?;
  requires store_wf(ns, s);
  requires typeok(nt, Context([]), s, t, T);
  requires step(t, s) == Some(P(t', s'));
  ensures store_extends(s', s);
  ensures store_wf(ns', s');
  ensures typeok(nt', Context([]), s', t', T);
{
  var ns'_ := lemma_store_wf_new(s, ns, s', t, T, nt, t');
  ns' := ns'_;
  var y := fresh_from(dom(Context([]))+tm_vars(t)+tp_vars(T));
  var t'_ := tm_subst(t.y, pt_var(y), t.t');
  assert typeok(nt-1, context_extend(Context([]), y, t.b.Tc), s, t'_, T);
  var nt_ := lemma_store_invariance_typeok(context_extend(Context([]), y, t.b.Tc), s, s', ns', t'_, T, nt-1);
  assert typing(0, Context([]), s', pt_loc(|s.m|), t.b.Tc);
  assert wfe_type(nt-1, Context([]), s, t.b.Tc);
  var nTwf_ := lemma_store_invariance_wfe_type(Context([]), s, s', ns', t.b.Tc, nt-1);
  assert subtype(nTwf_+1, Context([]), s', t.b.Tc, t.b.Tc);
  var nt'_ := lemma_subst(s', ns', t'_, T, nt_, y, t.b.Tc, tm_path(pt_loc(|s.m|)), nTwf_+2);
  assert typeok(nt'_, Context([]), s', tm_subst(y, pt_loc(|s.m|), t'_), T);
  nt' := nt'_;
  lemma_fresh_subst_typeok(Context([]), s', t, T, pt_loc(|s.m|), y, t'_, nt');
}

ghost method helper_typeok_path(nt: nat, ns: nat, ctx: context, s: store, p: pt, T: tp, T': tp) returns (nok: nat)
  requires typing(nt, ctx, s, p, T);
  requires subtype(ns, ctx, s, T, T');
  ensures typeok(nok, ctx, s, tm_path(p), T');
{
  nok := nt+ns+1;
  lemma_typing_monotonic_plus(nt, nok-1, ctx, s, p, T);
  lemma_subtype_monotonic_plus(ns, nok-1, ctx, s, T, T');
  assert typing(nok-1, ctx, s, p, T) && subtype(nok-1, ctx, s, T, T');
  assert exists T :: typing(nok-1, ctx, s, p, T) && subtype(nok-1, ctx, s, T, T');
}

ghost method helper_typeok_snd(t: tm, nm: nat, na: nat, nt': nat, ctx: context, s: store, y: nat, o: pt, m: nat, a: pt, t'_: tm, T: tp, P_: tp, R: tp) returns (nok: nat)
  requires t.tm_bind? && t.b.bd_snd?;
  requires y == fresh_from(dom(ctx)+tm_vars(t)+tp_vars(T));
  requires t'_ == tm_subst(t.y, pt_var(y), t.t');
  requires o==t.b.o;
  requires m==t.b.m;
  requires a==t.b.a;
  requires method_membership(nm, ctx, s, o, m, P_, R);
  requires typeok(na, ctx, s, tm_path(a), P_);
  requires typeok(nt', context_extend(ctx, y, R), s, t'_, T);
  ensures typeok(nok, ctx, s, t, T);
{
  nok := nm+na+nt'+1;
  lemma_method_membership_monotonic_plus(nm, nok-1, ctx, s, o, m, P_, R);
  lemma_typeok_monotonic_plus(na, nok-1, ctx, s, tm_path(a), P_);
  lemma_typeok_monotonic_plus(nt', nok-1, context_extend(ctx, y, R), s, t'_, T);
  assert method_membership(nok-1, ctx, s, o, m, P_, R) && typeok(nok-1, ctx, s, tm_path(a), P_) && typeok(nok-1, context_extend(ctx, y, R), s, t'_, T);
  assert exists P_, R :: method_membership(nok-1, ctx, s, o, m, P_, R) && typeok(nok-1, ctx, s, tm_path(a), P_) && typeok(nok-1, context_extend(ctx, y, R), s, t'_, T);
}

ghost method helper_typeok_exe(t: tm, nm: nat, nb: nat, nt': nat, ctx: context, s: store, y: nat, t'_: tm, T: tp, P_: tp, R: tp) returns (nok: nat)
  requires t.tm_bind? && t.b.bd_exe?;
  requires y == fresh_from(dom(ctx)+tm_vars(t)+tp_vars(T));
  requires t'_ == tm_subst(t.y, pt_var(y), t.t');
  requires method_membership(nm, ctx, s, pt_loc(t.b.ov), t.b.mv, P_, R);
  requires typeok(nb, ctx, s, t.b.t', R);
  requires typeok(nt', context_extend(ctx, y, R), s, t'_, T);
  ensures typeok(nok, ctx, s, t, T);
{
  nok := nm+nb+nt'+1;
  lemma_method_membership_monotonic_plus(nm, nok-1, ctx, s, pt_loc(t.b.ov), t.b.mv, P_, R);
  lemma_typeok_monotonic_plus(nb, nok-1, ctx, s, t.b.t', R);
  lemma_typeok_monotonic_plus(nt', nok-1, context_extend(ctx, y, R), s, t'_, T);
  assert method_membership(nok-1, ctx, s, pt_loc(t.b.ov), t.b.mv, P_, R) && typeok(nok-1, ctx, s, t.b.t', R) && typeok(nok-1, context_extend(ctx, y, R), s, t'_, T);
  assert exists P_, R :: method_membership(nok-1, ctx, s, pt_loc(t.b.ov), t.b.mv, P_, R) && typeok(nok-1, ctx, s, t.b.t', R) && typeok(nok-1, context_extend(ctx, y, R), s, t'_, T);  
}

ghost method helper_y_same(ctx: context, s: store, ns: nat, t: tm, t': tm, T: tp)
  requires t.tm_bind? && t'.tm_bind?;
  requires store_wf(ns, s);
  requires step(t, s).Some? && step(t, s).get.fst == t';
  requires t.t' == t'.t';
  ensures fresh_from(dom(ctx)+tm_vars(t)+tp_vars(T)) == fresh_from(dom(ctx)+tm_vars(t')+tp_vars(T));
{
  // TODO: follows from stepping of close sub-expressions
  assume fresh_from(dom(ctx)+tm_vars(t)+tp_vars(T)) == fresh_from(dom(ctx)+tm_vars(t')+tp_vars(T));
}

ghost method theorem_preservation_snd(s: store, ns: nat, t: tm, T: tp, nt: nat, t': tm, s': store) returns (ns': nat, nt': nat)
  requires t.tm_bind? && t.b.bd_snd?;
  requires store_wf(ns, s);
  requires typeok(nt, Context([]), s, t, T);
  requires step(t, s) == Some(P(t', s'));
  ensures store_extends(s', s);
  ensures store_wf(ns', s');
  ensures typeok(nt', Context([]), s', t', T);
{
  var ctx := Context([]);
  ns' := ns;
  assert t.y == t'.y;
  assert t.t' == t.t';
  var y := fresh_from(dom(ctx)+tm_vars(t)+tp_vars(T));
  helper_y_same(ctx, s, ns, t, t', T);
  var t'_ := tm_subst(t.y, pt_var(y), t.t');
  var P, R :| method_membership(nt-1, ctx, s, t.b.o, t.b.m, P, R) &&
    typeok(nt-1, ctx, s, tm_path(t.b.a), P) &&
    typeok(nt-1, context_extend(ctx, y, R), s, t'_, T);
  if (pt_step(t.b.o, s).Some?) {
    assert membership(nt-2, ctx, s, t.b.o, t.b.m, decl_mt(t.b.m, P, R));
    assert exists To :: typing(nt-3, ctx, s, t.b.o, To);
    var To :| typing(nt-3, ctx, s, t.b.o, To);
    var o' := pt_step(t.b.o, s).get;
    var To', no' := theorem_pt_preservation(s, ns, t.b.o, To, nt-3, o');
    var P', R', nm' := lemma_subtype_inversion_method(ctx, s, nt-3, t.b.o, To, no', o', To', no', nt-1, t.b.m, P, R);
    assert method_membership(nm', ctx, s, o', t.b.m, P', R');
    assert exists Ta :: typing(nt-2, ctx, s, t.b.a, Ta) && subtype(nt-2, ctx, s, Ta, P);
    var Ta :| typing(nt-2, ctx, s, t.b.a, Ta) && subtype(nt-2, ctx, s, Ta, P);
    var na_ := theorem_subtype_transitive(ctx, s, nt-2, nm', Ta, P, P');
    var na := helper_typeok_path(nt-2, na_, ctx, s, t.b.a, Ta, P');
    assert typeok(na, ctx, s, tm_path(t.b.a), P');
    var nt'_ := lemma_subst_in_context(s, ns, t'_, T, nt-1, y, R, R', nm');
    assert typeok(nt'_, context_extend(ctx, y, R'), s, t'_, T);
    nt' := helper_typeok_snd(t', nm', na, nt'_, ctx, s, y, o', t.b.m, t.b.a, t'_, T, P', R');
  } else if (pt_step(t.b.a, s).Some?) {
    var Ta :| typing(nt-2, ctx, s, t.b.a, Ta) && subtype(nt-2, ctx, s, Ta, P);
    var a' := pt_step(t.b.a, s).get;
    var Ta', na' := theorem_pt_preservation(s, ns, t.b.a, Ta, nt-2, a');
    var na_ := theorem_subtype_transitive(ctx, s, na', nt-2, Ta', Ta, P);
    var na := helper_typeok_path(na', na_, ctx, s, a', Ta', P);
    nt' := helper_typeok_snd(t', nt-1, na, nt-1, ctx, s, y, t.b.o, t.b.m, a', t'_, T, P, R);
  } else {
    var x, body, nbody := lemma_store_wf_method_ok(ns, s, t.b.o.loc, t.b.m, nt-1, P, R);
    var nbody' := lemma_subst(s, ns, body, R, nbody, x, P, tm_path(t.b.a), nt-1);
    nt' := helper_typeok_exe(t', nt-1, nbody', nt-1, ctx, s, y, t'_, T, P, R);
  }
}

ghost method theorem_preservation(s: store, ns: nat, t: tm, T: tp, nt: nat, t': tm, s': store) returns (ns': nat, nt': nat)
  requires store_wf(ns, s);
  requires typeok(nt, Context([]), s, t, T);
  requires step(t, s) == Some(P(t', s'));
  ensures store_extends(s', s);
  ensures store_wf(ns', s');
  ensures typeok(nt', Context([]), s', t', T);
{
  if (t.tm_path?) {
    ns', nt' := theorem_preservation_path(s, ns, t, T, nt, t', s');
  } else if (t.tm_bind? && t.b.bd_new?) {
    ns', nt' := theorem_preservation_new(s, ns, t, T, nt, t', s');
  } else if (t.tm_bind? && t.b.bd_snd?) {
    ns', nt' := theorem_preservation_snd(s, ns, t, T, nt, t', s');
  } else {
    var y := fresh_from(dom(Context([]))+tm_vars(t)+tp_vars(T));
    var t'_ := tm_subst(t.y, pt_var(y), t.t');
    var P, R :| method_membership(nt-1, Context([]), s, pt_loc(t.b.ov), t.b.mv, P, R) &&
      typeok(nt-1, Context([]), s, t.b.t', R) &&
      typeok(nt-1, context_extend(Context([]), y, R), s, t'_, T);
    if (step(t.b.t', s).Some?) {
      helper_y_same(Context([]), s, ns, t, t', T);
      var bt'_ := step(t.b.t', s).get.fst;
      var bs'_ := step(t.b.t', s).get.snd;
      assert s' == bs'_;
      var nbs'_, nbt'_ := theorem_preservation(s, ns, t.b.t', R, nt-1, bt'_, bs'_);
      ns' := nbs'_;
      assert method_membership(nt-1, Context([]), s, pt_loc(t'.b.ov), t'.b.mv, P, R);
      var nm_ := lemma_store_invariance_method_membership(Context([]), s, s', ns', pt_loc(t'.b.ov), t'.b.mv, P, R, nt-1);
      assert method_membership(nm_, Context([]), s', pt_loc(t'.b.ov), t'.b.mv, P, R);
      assert typeok(nbt'_, Context([]), s', t'.b.t', R);
      assert typeok(nt-1, context_extend(Context([]), y, R), s, t'_, T);
      var nt'_ := lemma_store_invariance_typeok(context_extend(Context([]), y, R), s, s', ns', t'_, T, nt-1);
      nt' := helper_typeok_exe(t', nm_, nbt'_, nt'_, Context([]), s', y, t'_, T, P, R);
    } else {
      ns' := ns;
      nt' := lemma_subst(s, ns, t'_, T, nt-1, y, R, t.b.t', nt-1);
      lemma_fresh_subst_typeok(Context([]), s, t, T, t.b.t'.p, y, t'_, nt');
    }
  }
}
