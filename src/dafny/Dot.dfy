// Utilities

// List
datatype list<A> = Nil | Cons(head: A, tail: list<A>);
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

// Partial Maps
datatype partial_map<A> = Empty | Extend(x: nat, v: A, rest: partial_map<A>);
function lookup<A>(x: nat, m: partial_map<A>): option<A>
{
  match m
  case Empty => None
  case Extend(x', v, rest) => if x==x' then Some(v) else lookup(x, rest)
}

// Syntax
datatype tp = tp_sel_c(pc: tm, Lc: nat) | tp_sel_a(pa: tm, La: nat) | tp_rfn(base_tp: tp, self: nat, decls: list<decl>) | tp_and(and1: tp, and2: tp) | tp_or(or1: tp, or2: tp) | tp_top | tp_bot;
datatype tm = tm_loc(loc: nat) | tm_var(x: nat) | tm_new(y: nat, Tc: tp, init: list<def>, t': tm) | tm_sel(t: tm, l: nat) | tm_msel(o: tm, m: nat, a: tm);
datatype decl = decl_tp_c(Lc: nat, Sc: tp, Uc: tp) | decl_tp_a(La: nat, Sa: tp, Ua: tp) | decl_tm(l: nat, T: tp) | decl_mt(m: nat, P: tp, R: tp);
datatype def = def_tm(l: nat, t: tm) | def_mt(m: nat, param: nat, body: tm);

predicate path(t: tm)
{
  t.tm_loc? || t.tm_var? || (t.tm_sel? && path(t.t))
}

predicate concrete(T: tp)
{
  (T.tp_sel_c? && path(T.pc)) ||
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
  case tm_new(y, Tc, init, t') => tm_new(y, tp_subst(x, v, Tc), if y==x then init else defs_subst(x, v, init), if y==x then t' else tm_subst(x, v, t'))
  case tm_sel(t1, l) => tm_sel(tm_subst(x, v, t1), l)
  case tm_msel(o, m, a) => tm_msel(tm_subst(x, v, o), m, tm_subst(x, v, a))
}
function tp_subst(x: nat, v: tm, T: tp): tp
{
  match T
  case tp_sel_c(pc, Lc) => tp_sel_c(tm_subst(x, v, pc), Lc)
  case tp_sel_a(pa, La) => tp_sel_a(tm_subst(x, v, pa), La)
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
  case decl_tp_c(Lc, Sc, Uc) => decl_tp_c(Lc, tp_subst(x, v, Sc), tp_subst(x, v, Uc))
  case decl_tp_a(La, Sa, Ua) => decl_tp_a(La, tp_subst(x, v, Sa), tp_subst(x, v, Ua))
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
// Free variables
// fn(x, A) <==> x appears free in A
predicate tm_fn(x: nat, t: tm)
{
  match t
  case tm_loc(loc) => false
  case tm_var(x') => x'==x
  case tm_new(y, Tc, init, t') => tp_fn(x, Tc) || (y!=x && (defs_fn(x, init) || tm_fn(x, t')))
  case tm_sel(t1, l) => tm_fn(x, t1)
  case tm_msel(o, m, a) => tm_fn(x, o) || tm_fn(x, a)
}
predicate tp_fn(x: nat, T: tp)
{
  match T
  case tp_sel_c(pc, Lc) => tm_fn(x, pc)
  case tp_sel_a(pa, La) => tm_fn(x, pa)
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
  case decl_tp_c(Lc, Sc, Uc) => tp_fn(x, Sc) || tp_fn(x, Uc)
  case decl_tp_a(La, Sa, Ua) => tp_fn(x, Sa) || tp_fn(x, Ua)
  case decl_tm(l, T) => tp_fn(x, T)
  case decl_mt(m, P, R) => tp_fn(x, P) || tp_fn(x, R)
}
predicate defs_fn(x: nat, defs: list<def>)
{
  match defs
  case Nil => false
  case Cons(head, tail) => def_fn(x, head) || defs_fn(x, tail)
}
predicate decls_fn(x: nat, decls: list<decl>)
{
  match decls
  case Nil => false
  case Cons(head, tail) => decl_fn(x, head) || decls_fn(x, tail)
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
              Store(snoc(s.lst, P(t.Tc, defs_subst(t.y, tm_loc(length(s.lst)), t.init))))))
  else None
}

// Type System

// Context
datatype context = Context(m: partial_map<tp>);

// Typing-Related Judgments

copredicate typing(ctx: context, t: tm, T: tp)
{
  match t
  case tm_loc(loc) => false // locations are not part of user programs
  case tm_var(x) => lookup(x, ctx.m) == Some(T)
  case tm_new(y, Tc, init, t') =>
    exists Ds ::
    typing(Context(Extend(y, Tc, ctx.m)), t', T) &&
    wfe_type(ctx, Tc) &&
    expansion(ctx, y, Tc, Ds) && 
    wf_init(Ds, init) &&
    !tp_fn(y, T)
  case tm_sel(t, l) =>
    field_membership(ctx, t, l, T)
  case tm_msel(o, m, a) =>
    exists S, T' :: method_membership(ctx, o, m, S, T) &&
    typing(ctx, a, T') &&
    subtype(ctx, T', S)
}
predicate wf_init(decls: list<decl>, defs: list<def>)
{
  true // TODO
}
copredicate wf_decl(ctx: context, d: decl)
{
  match d
  case decl_tp_c(L, S, U) => wf_type(ctx, S) && wf_type(ctx, U)
  case decl_tp_a(L, S, U) => wf_type(ctx, S) && wf_type(ctx, U)
  case decl_tm(l, T) => wf_type(ctx, T)
  case decl_mt(m, S, T) => wf_type(ctx, S) && wf_type(ctx, T)
}
copredicate wf_decls(ctx: context, Ds: list<decl>)
{
  match Ds
  case Nil => true
  case Cons(head, tail) => wf_decl(ctx, head) && wf_decls(ctx, tail)
}
copredicate wf_type_sel(ctx: context, p: tm, L: nat)
{
  path(p) &&
  exists S, U :: type_membership(ctx, p, L, S, U) &&
  (S==tp_bot ||
  (wf_type(ctx, S) && wf_type(ctx, U)))
}
copredicate wf_type(ctx: context, T: tp)
{
  match T
  case tp_rfn(T', z, Ds) =>
    wf_type(ctx, T') && wf_decls(Context(Extend(z, T, ctx.m)), Ds)
  case tp_sel_c(p, L) => wf_type_sel(ctx, p, L)
  case tp_sel_a(p, L) => wf_type_sel(ctx, p, L)
  case tp_and(T1, T2) => wf_type(ctx, T1) && wf_type(ctx, T2)
  case tp_or(T1, T2) => wf_type(ctx, T1) && wf_type(ctx, T2)
  case tp_top => true
  case tp_bot => true
}
predicate wfe_type(ctx: context, T: tp)
{
  wf_type(ctx, T) && exists Ds :: expansion(ctx, 0, T, Ds)
}
predicate membership(ctx: context, t: tm, l: nat, d: decl)
{
  false
}
predicate field_membership(ctx: context, t: tm, l: nat, T: tp)
{
  exists d :: membership(ctx, t, l, d) &&
  d.decl_tm? && d.l==l && d.T==T
}
predicate method_membership(ctx: context, t: tm, m: nat, P: tp, R: tp)
{
  exists d :: membership(ctx, t, m, d) &&
  d.decl_mt? && d.m==m && d.P==P && d.R==R
}
predicate type_membership(ctx: context, t: tm, L: nat, S: tp, U: tp)
{
  exists d :: membership(ctx, t, L, d) &&
  ((d.decl_tp_c? && d.Lc==L && d.Sc==S && d.Uc==U) ||
   (d.decl_tp_a? && d.La==L && d.Sa==S && d.Ua==U))
}
copredicate expansion(ctx: context, z: nat, T: tp, Ds: list<decl>)
{
  true // TODO
}
predicate subtype(ctx: context, S: tp, T: tp)
{
  true // TODO
}
