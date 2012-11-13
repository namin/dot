// Utilities

// List
datatype list<A> = Nil | Cons(head: A, tail: list<A>);
// list functions
function length<A>(lst: list<A>): nat
  ensures length(lst)==0 ==> lst.Nil?;
  ensures length(lst)>0 ==> lst.Cons?;
{
  match lst
  case Nil => 0
  case Cons(head, tail) => 1 + length(tail)
}
function nth<A>(n: nat, lst: list<A>): A
  requires n < length(lst);
{
  if (n==0) then lst.head else nth(n-1, lst.tail)
}
function snoc<A>(lst: list<A>, x: A): list<A>
{
  match lst
  case Nil => Cons(x, Nil)
  case Cons(head, tail) => Cons(head, snoc(tail, x))
}

// Pair
datatype pair<A, B> = P(fst: A, snd: B);

// Option
datatype option<A> = None | Some(get: A);

// Syntax
datatype tp_label = lc(lc: nat) | la(la: nat);
datatype tp = tp_sel(p: tm, L: tp_label) | tp_rfn(base_tp: tp, self: nat, decls: list<decl>) | tp_and(and1: tp, and2: tp) | tp_or(or1: tp, or2: tp) | tp_top | tp_bot;
datatype tm = tm_loc(loc: nat) | tm_var(x: nat) | tm_new(y: nat, T: tp, init: list<def>, t': tm) | tm_sel(t: tm, l: nat) | tm_msel(o: tm, m: nat, a: tm);
datatype decl = decl_tp(L: tp_label, S: tp, U: tp) | decl_tm(l: nat, T: tp) | decl_mt(m: nat, P: tp, R: tp);
datatype def = def_tm(l: nat, t: tm) | def_mt(m: nat, param: nat, body: tm);

predicate concrete_label(l: tp_label)
{
  l.lc?
}

predicate path(t: tm)
{
  t.tm_loc? || t.tm_var? || (t.tm_sel? && path(t.t))
}

predicate concrete(T: tp)
{
  (T.tp_sel? && path(T.p) && concrete_label(T.L)) ||
  (T.tp_rfn? && concrete(T.base_tp)) ||
  (T.tp_and? && concrete(T.and1) && concrete(T.and2)) ||
  T.tp_top?
}

// Operational Semantics

// Values
predicate value(t: tm)
{
  t.tm_loc?
}

// Store
datatype store = Store(lst: list<pair<tp, list<def>>>);
function store_lookup(n: nat, s: store): list<def>
  requires n < length(s.lst);
{
  nth(n, s.lst).snd
}
function def_method_lookup(m: nat, defs: list<def>): option<pair<int, tm>>
  ensures def_method_lookup(m, defs).Some? ==> def_method_lookup(m, defs).get.fst>=0;
{
  match defs
  case Nil => None
  case Cons(head, tail) =>
    if (head.def_mt? && head.m==m) then Some(P(head.param, head.body))
    else def_method_lookup(m, tail)
}
function def_field_lookup(l: nat, defs: list<def>): option<tm>
{
  match defs
  case Nil => None
  case Cons(head, tail) =>
    if (head.def_tm? && head.l==l) then Some(head.t)
    else def_field_lookup(l, tail)
}

// Substitution
function tm_subst(x: nat, v: tm, t: tm): tm
{
  match t
  case tm_loc(loc) => t
  case tm_var(x') => if x'==x then v else t
  case tm_new(y, T, init, t') => tm_new(y, tp_subst(x, v, T), if y==x then init else defs_subst(x, v, init), if y==x then t' else tm_subst(x, v, t'))
  case tm_sel(t1, l) => tm_sel(tm_subst(x, v, t1), l)
  case tm_msel(o, m, a) => tm_msel(tm_subst(x, v, o), m, tm_subst(x, v, a))
}
function tp_subst(x: nat, v: tm, T: tp): tp
{
  match T
  case tp_sel(p, L) => tp_sel(tm_subst(x, v, p), L)
  case tp_rfn(base_tp, self, decls) => tp_rfn(tp_subst(x, v, base_tp), self, if self==x then decls else decls_subst(x, v, decls))
  case tp_and(and1, and2) => tp_and(tp_subst(x, v, and1), tp_subst(x, v, and2))
  case tp_or(or1, or2) => tp_or(tp_subst(x, v, or1), tp_subst(x, v, or2))
  case tp_top => T
  case tp_bot => T
}
function def_subst(x: nat, v: tm, d: def): def
{
  match d
  case def_tm(l, t1) => def_tm(l, tm_subst(x, v, t1))
  case def_mt(m, param, body) => if param==x then d else def_mt(m, param, tm_subst(x, v, body))
}
function decl_subst(x: nat, v: tm, d: decl): decl
{
  match d
  case decl_tp(L, S, U) => decl_tp(L, tp_subst(x, v, S), tp_subst(x, v, U))
  case decl_tm(l, T) => decl_tm(l, tp_subst(x, v, T))
  case decl_mt(m, P, R) => decl_mt(m, tp_subst(x, v, P), tp_subst(x, v, R))
}
function defs_subst(x: nat, v: tm, defs: list<def>): list<def>
{
  match defs
  case Nil => Nil
  case Cons(head, tail) => Cons(def_subst(x, v, head), defs_subst(x, v, tail))
}
function decls_subst(x: nat, v: tm, decls: list<decl>): list<decl>
{
  match decls
  case Nil => Nil
  case Cons(head, tail) => Cons(decl_subst(x, v, head), decls_subst(x, v, tail))
}

// Reduction
function step(t: tm, s: store): option<pair<tm, store>>
{
  /* msel */
  if (t.tm_msel? && t.o.tm_loc? && value(t.a) && t.o.loc < length(s.lst) &&
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
  else if (t.tm_sel? && t.t.tm_loc? && t.t.loc < length(s.lst) &&
           def_field_lookup(t.l, store_lookup(t.t.loc, s)).Some?)
  then Some(P(def_field_lookup(t.l, store_lookup(t.t.loc, s)).get, s))
  /* sel1 */
  else if (t.tm_sel? && step(t.t, s).Some?)
  then Some(P(tm_sel(step(t.t, s).get.fst, t.l), step(t.t, s).get.snd))
  /* new */
  else if (t.tm_new?)
  then Some(P(tm_subst(t.y, tm_loc(length(s.lst)), t.t'),
              Store(snoc(s.lst, P(t.T, defs_subst(t.y, tm_loc(length(s.lst)), t.init))))))
  else None
}