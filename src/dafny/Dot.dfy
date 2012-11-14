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
function slice<A>(i: nat, j: nat, lst: list<A>): list<A>
  requires 0 <= i <= j <= length(lst);
  decreases j-i;
{
  if (i==j) then Nil
  else if (i==0) then Cons(lst.head, slice(i, j-1, lst.tail))
  else slice(i+1, j, lst)
}
function snoc<A>(lst: list<A>, x: A): list<A>
{
  match lst
  case Nil => Cons(x, Nil)
  case Cons(head, tail) => Cons(head, snoc(tail, x))
}
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
predicate same_lst_seq<A>(lst: list<A>, s: seq<A>)
  ensures same_lst_seq(lst, s) ==> length(lst)==|s|;
{
  match lst
  case Nil => s==[]
  case Cons(head, tail) => |s|>0 && s[0]==head && same_lst_seq(tail, s[1..])
}
ghost method lemma_lst2seq_same<A>(lst: list<A>, s: seq<A>)
  requires lst2seq(lst)==s;
  ensures same_lst_seq(lst, s);
{
}
ghost method lemma_same_lst_seq_forall<A>(lst: list<A>, s: seq<A>)
  requires same_lst_seq(lst, s );
  ensures forall n :: 0 <= n < |s| ==> s[n]==nth(n, lst);
{
  match lst {
  case Nil =>
  case Cons(head, tail) =>
    assert s[0]==head;
    lemma_same_lst_seq_forall(tail, s[1..]);
  }
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
function dom<A>(m: partial_map<A>): seq<int>
  ensures forall x :: x in dom(m) ==> x>=0;
{
  match m
  case Empty => []
  case Extend(x, v, rest) => [x]+dom(rest)
}

// Syntax
datatype tp = tp_sel_c(pc: tm, Lc: nat) | tp_sel_a(pa: tm, La: nat) | tp_rfn(base_tp: tp, self: nat, decls: list<decl>) | tp_and(and1: tp, and2: tp) | tp_or(or1: tp, or2: tp) | tp_top | tp_bot;
datatype tm = tm_loc(loc: nat) | tm_var(x: nat) | tm_new(y: nat, Tc: tp, init: list<def>, t': tm) | tm_sel(t: tm, l: nat) | tm_msel(o: tm, m: nat, a: tm);
datatype decl = decl_tp_c(Lc: nat, Sc: tp, Uc: tp) | decl_tp_a(La: nat, Sa: tp, Ua: tp) | decl_tm(l: nat, T: tp) | decl_mt(m: nat, P: tp, R: tp);
datatype def = def_tm(l: nat, t: tm) | def_mt(m: nat, param: nat, body: tm);
datatype decls = decls_fin(decls: seq<decl>) | decls_bot;

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

function decl_label(d: decl): nat
{
  match d
  case decl_tp_c(Lc, Sc, Uc) => Lc
  case decl_tp_a(La, Sa, Ua) => La
  case decl_tm(l, T) => l
  case decl_mt(m, P, R) => m
}

// Sorting-related functions
predicate decl_lt(d1: decl, d2: decl)
{
  match d1
  case decl_tp_c(Lc1, Sc1, Uc1) =>
    (match d2
     case decl_tp_c(Lc2, Sc2, Uc2) => Lc1<Lc2
     case decl_tp_a(La2, Sa2, Ua2) => true
     case decl_tm(l2, T2) => true
     case decl_mt(m2, P2, R2) => true)
  case decl_tp_a(La1, Sa1, Ua1) =>
    (match d2
     case decl_tp_c(Lc2, Sc2, Uc2) => false
     case decl_tp_a(La2, Sa2, Ua2) => La1<La2
     case decl_tm(l2, T2) => true
     case decl_mt(m2, P2, R2) => true)
  case decl_tm(l1, T1) =>
    (match d2
     case decl_tp_c(Lc2, Sc2, Uc2) => false
     case decl_tp_a(La2, Sa2, Ua2) => false
     case decl_tm(l2, T2) => l1<l2
     case decl_mt(m2, P2, R2) => true)
  case decl_mt(m1, P1, R1) =>
    (match d2
     case decl_tp_c(Lc2, Sc2, Uc2) => false
     case decl_tp_a(La2, Sa2, Ua2) => false
     case decl_tm(l2, T2) => false
     case decl_mt(m2, P2, R2) => m1<m2)    
}
predicate decl_eq(d1: decl, d2: decl)
  ensures d1==d2 ==> decl_eq(d1, d2);
  ensures decl_eq(d1, d2) ==> decl_label(d1)==decl_label(d2);
  ensures decl_eq(d1, d2) ==> d1.decl_tp_c?==d2.decl_tp_c?;
  ensures decl_eq(d1, d2) ==> d1.decl_tp_a?==d2.decl_tp_a?;
  ensures decl_eq(d1, d2) ==> d1.decl_tm?==d2.decl_tm?;
  ensures decl_eq(d1, d2) ==> d1.decl_mt?==d2.decl_mt?;
  ensures decl_eq(d1, d2) ==> !decl_lt(d1, d2) && !decl_lt(d2, d1);
{
  match d1
  case decl_tp_c(Lc1, Sc1, Uc1) => d2.decl_tp_c? && d2.Lc==Lc1
  case decl_tp_a(La1, Sa1, Ua1) => d2.decl_tp_a? && d2.La==La1
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
predicate decl_lst_sorted(lst: list<decl>)
{
  match lst
  case Nil => true
  case Cons(x, tail) =>
    (match tail
     case Nil => true
     case Cons(y, tail') => decl_le(x, y) && decl_lst_sorted(tail))
}
function decl_lst_sort(lst: list<decl>): list<decl>
{
  seq2lst(decl_seq_sort(lst2seq(lst)))
}
ghost method lemma_decl_le_trans(d1: decl, d2: decl, d3: decl)
  requires decl_le(d1, d2);
  requires decl_le(d2, d3);
  ensures decl_le(d1, d3);
{
}
ghost method lemma_decl_le_comparable(d1: decl, d2: decl)
  requires !decl_le(d1, d2);
  ensures decl_le(d2, d1);
{
}
ghost method lemma_decl_seq_merging(s1: seq<decl>, s2: seq<decl>)
  requires decl_seq_sorted(s1) && decl_seq_sorted(s2);
  ensures decl_seq_sorted(decl_seq_merge(s1, s2));
  ensures multiset((s1+s2)[..]) == multiset(decl_seq_merge(s1,s2)[..]);
{
  if (s1 == []) {}
  else if (s2 == []) {}
  else if (decl_le(s1[0], s2[0])) {
    parallel (n | 0 <= n < |s1|)
      ensures decl_le(s1[0], s1[n]);
    {
    }
    parallel (n | 0 <= n < |s2|)
      ensures decl_le(s1[0], s2[n]);
    {
      lemma_decl_le_trans(s1[0], s2[0], s2[n]);
    }
    var sm := decl_seq_merge(s1[1..], s2);
    lemma_decl_seq_merging(s1[1..], s2);
    var s := [s1[0]]+sm;
    assert decl_le(s1[0], sm[0]);
    parallel (m,n | 0 <= m < n < |s|)
      ensures decl_le(s[m], s[n]);
    {
      if (m==0) {
        lemma_decl_le_trans(s1[0], sm[0], s[n]);
      }
    }
  } else {
    lemma_decl_le_comparable(s1[0], s2[0]);
    parallel (n | 0 <= n < |s2|)
      ensures decl_le(s2[0], s2[n]);
    {
    }
    parallel (n | 0 <= n < |s1|)
      ensures decl_le(s2[0], s1[n]);
    {
      lemma_decl_le_trans(s2[0], s1[0], s1[n]);
    }
    var sm := decl_seq_merge(s1, s2[1..]);
    lemma_decl_seq_merging(s1, s2[1..]);
    var s := [s2[0]]+sm;
    assert decl_le(s2[0], sm[0]);
    parallel (m,n | 0 <= m < n < |s|)
      ensures decl_le(s[m], s[n]);
    {
      if (m==0) {
        lemma_decl_le_trans(s2[0], sm[0], s[n]);
      }
    }
  }  
}
ghost method lemma_decl_seq_sorting(s: seq<decl>)
  ensures decl_seq_sorted(decl_seq_sort(s));
  ensures multiset(s[..]) == multiset(decl_seq_sort(s)[..]);
{
  if (s == []) {}
  else {
    var i: nat := (|s|-1)/2;
    lemma_decl_seq_sorting(s[..i]);
    lemma_decl_seq_sorting(s[i+1..]);
    lemma_decl_seq_merging(decl_seq_sort(s[..i]), decl_seq_sort(s[i+1..]));    
  }
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
ghost method lemma_def_le_trans(d1: def, d2: def, d3: def)
  requires def_le(d1, d2);
  requires def_le(d2, d3);
  ensures def_le(d1, d3);
{
}
ghost method lemma_def_le_comparable(d1: def, d2: def)
  requires !def_le(d1, d2);
  ensures def_le(d2, d1);
{
}
ghost method lemma_def_seq_merging(s1: seq<def>, s2: seq<def>)
  requires def_seq_sorted(s1) && def_seq_sorted(s2);
  ensures def_seq_sorted(def_seq_merge(s1, s2));
  ensures multiset((s1+s2)[..]) == multiset(def_seq_merge(s1,s2)[..]);
{
  if (s1 == []) {}
  else if (s2 == []) {}
  else if (def_le(s1[0], s2[0])) {
    parallel (n | 0 <= n < |s1|)
      ensures def_le(s1[0], s1[n]);
    {
    }
    parallel (n | 0 <= n < |s2|)
      ensures def_le(s1[0], s2[n]);
    {
      lemma_def_le_trans(s1[0], s2[0], s2[n]);
    }
    var sm := def_seq_merge(s1[1..], s2);
    lemma_def_seq_merging(s1[1..], s2);
    var s := [s1[0]]+sm;
    assert def_le(s1[0], sm[0]);
    parallel (m,n | 0 <= m < n < |s|)
      ensures def_le(s[m], s[n]);
    {
      if (m==0) {
        lemma_def_le_trans(s1[0], sm[0], s[n]);
      }
    }
  } else {
    lemma_def_le_comparable(s1[0], s2[0]);
    parallel (n | 0 <= n < |s2|)
      ensures def_le(s2[0], s2[n]);
    {
    }
    parallel (n | 0 <= n < |s1|)
      ensures def_le(s2[0], s1[n]);
    {
      lemma_def_le_trans(s2[0], s1[0], s1[n]);
    }
    var sm := def_seq_merge(s1, s2[1..]);
    lemma_def_seq_merging(s1, s2[1..]);
    var s := [s2[0]]+sm;
    assert def_le(s2[0], sm[0]);
    parallel (m,n | 0 <= m < n < |s|)
      ensures def_le(s[m], s[n]);
    {
      if (m==0) {
        lemma_def_le_trans(s2[0], sm[0], s[n]);
      }
    }
  }  
}
ghost method lemma_def_seq_sorting(s: seq<def>)
  ensures def_seq_sorted(def_seq_sort(s));
  ensures multiset(s[..]) == multiset(def_seq_sort(s)[..]);
{
  if (s == []) {}
  else {
    var i: nat := (|s|-1)/2;
    lemma_def_seq_sorting(s[..i]);
    lemma_def_seq_sorting(s[i+1..]);
    lemma_def_seq_merging(def_seq_sort(s[..i]), def_seq_sort(s[i+1..]));    
  }
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
  defs.Cons? && (def_fn(x, defs.head) || defs_fn(x, defs.tail))
}
predicate decls_fn(x: nat, decls: list<decl>)
{
  decls.Cons? && (decl_fn(x, decls.head) || decls_fn(x, decls.tail))
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

// Declaration Lattice
predicate decl_bot(d: decl)
{
  match d
  case decl_tp_c(L, S, U) => S==tp_top && U==tp_bot
  case decl_tp_a(L, S, U) => S==tp_top && U==tp_bot
  case decl_tm(l, T) => T==tp_bot
  case decl_mt(m, S, U) => S==tp_top && U==tp_bot
}
function decl_and(d1: decl, d2: decl): decl
  requires decl_eq(d1, d2);
  ensures decl_eq(d1, decl_and(d1, d2));
  ensures decl_eq(d2, decl_and(d1, d2));
{
  match d1
  case decl_tp_c(L, S, U) => decl_tp_c(L, tp_or(S, d2.Sc), tp_and(U, d2.Uc))
  case decl_tp_a(L, S, U) => decl_tp_a(L, tp_or(S, d2.Sa), tp_and(U, d2.Ua))
  case decl_tm(l, U) => decl_tm(l, tp_and(U, d2.T))
  case decl_mt(m, S, U) => decl_mt(m, tp_or(S, d2.P), tp_and(U, d2.R))
}
function decl_or(d1: decl, d2: decl): decl
  requires decl_eq(d1, d2);
  ensures decl_eq(d1, decl_or(d1, d2));
  ensures decl_eq(d2, decl_or(d1, d2));
{
  match d1
  case decl_tp_c(L, S, U) => decl_tp_c(L, tp_and(S, d2.Sc), tp_or(U, d2.Uc))
  case decl_tp_a(L, S, U) => decl_tp_a(L, tp_and(S, d2.Sa), tp_or(U, d2.Ua))
  case decl_tm(l, U) => decl_tm(l, tp_or(U, d2.T))
  case decl_mt(m, S, U) => decl_mt(m, tp_and(S, d2.P), tp_or(U, d2.R))
}
function decls_fin_and(s1: seq<decl>, s2: seq<decl>): seq<decl>
  requires decl_seq_sorted(s1);
  requires decl_seq_sorted(s2);
  //ensures decl_seq_sorted(decls_fin_and(s1, s2));
{
        if (s1 == []) then s2
  else  if (s2 == []) then s1
  else  if (decl_eq(s1[0], s2[0])) then   [decl_and(s1[0], s2[0])]+decls_fin_and(s1[1..], s2[1..])
  else  if (decl_lt(s1[0], s2[0])) then   [s1[0]]+decls_fin_and(s1[1..], s2)
  else/*if (decl_lt(s2[0], s1[0])) then*/ [s2[0]]+decls_fin_and(s1, s2[1..])
}
function decls_and(Ds1: decls, Ds2: decls): decls
  requires Ds1.decls_fin? ==> decl_seq_sorted(Ds1.decls);
  requires Ds2.decls_fin? ==> decl_seq_sorted(Ds2.decls);
  //ensures decls_and(Ds1, Ds2).decls_fin? ==> decl_seq_sorted(decls_and(Ds1, Ds2).decls); 
{
  match Ds1
  case decls_bot => decls_bot
  case decls_fin(s1) =>
    (match Ds2
     case decls_bot => decls_bot
     case decls_fin(s2) => decls_fin(decls_fin_and(s1, s2)))
}
function decls_fin_or(s1: seq<decl>, s2: seq<decl>): seq<decl>
  requires decl_seq_sorted(s1);
  requires decl_seq_sorted(s2);
  //ensures decl_seq_sorted(decls_fin_or(s1, s2));
{
        if (s1 == []) then []
  else  if (s2 == []) then []
  else  if (decl_eq(s1[0], s2[0])) then   [decl_or(s1[0], s2[0])]+decls_fin_and(s1[1..], s2[1..])
  else  if (decl_lt(s1[0], s2[0])) then   decls_fin_or(s1[1..], s2)
  else/*if (decl_lt(s2[0], s1[0])) then*/ decls_fin_or(s1, s2[1..])
}
function decls_or(Ds1: decls, Ds2: decls): decls
  requires Ds1.decls_fin? ==> decl_seq_sorted(Ds1.decls);
  requires Ds2.decls_fin? ==> decl_seq_sorted(Ds2.decls);
  //ensures decls_or(Ds1, Ds2).decls_fin? ==> decl_seq_sorted(decls_or(Ds1, Ds2).decls); 
{
  match Ds1
  case decls_bot => Ds2
  case decls_fin(s1) =>
    (match Ds2
     case decls_bot => Ds1
     case decls_fin(s2) => decls_fin(decls_fin_or(s1, s2)))
}

// Typing-Related Judgments

copredicate typing(ctx: context, t: tm, T: tp)
{
  match t
  case tm_loc(loc) => false // locations are not part of user programs
  case tm_var(x) => lookup(x, ctx.m) == Some(T)
  case tm_new(y, Tc, init, t') =>
    exists Ds:decls :: Ds.decls_fin? &&
    wfe_type(ctx, Tc) &&
    expansion(ctx, y, Tc, Ds) && 
    wf_init(Context(Extend(y, Tc, ctx.m)), Ds.decls, def_seq_sort(lst2seq(init))) &&
    !tp_fn(y, T) &&
    typing(Context(Extend(y, Tc, ctx.m)), t', T)
  case tm_sel(t, l) =>
    field_membership(ctx, t, l, T)
  case tm_msel(o, m, a) =>
    exists S, T' :: method_membership(ctx, o, m, S, T) &&
    typing(ctx, a, T') &&
    subtype(ctx, T', S)
}
copredicate wf_init(ctx: context, decls: seq<decl>, defs: seq<def>)
  //requires decl_seq_sorted(decls);
  //requires def_seq_sorted(defs);
{
  (decls==[] && defs==[]) || (|decls|>0 && (
    (((decls[0].decl_tp_c? && subtype(ctx, decls[0].Sc, decls[0].Uc)) ||
      (decls[0].decl_tp_a? && subtype(ctx, decls[0].Sa, decls[0].Ua))) &&
     wf_init(ctx, decls[1..], defs)) || (|defs|>0 && (
    ((decls[0].decl_tm? && defs[0].def_tm? && decls[0].l==defs[0].l &&
      value(defs[0].t) &&
      exists T :: typing(ctx, defs[0].t, T) &&
      subtype(ctx, T, decls[0].T)) ||
     (decls[0].decl_mt? && defs[0].def_mt? && decls[0].m==defs[0].m &&
      wfe_type(ctx, decls[0].P) &&
      exists T' :: typing(Context(Extend(defs[0].param, decls[0].P, ctx.m)), defs[0].body, T') &&
      subtype(Context(Extend(defs[0].param, decls[0].P, ctx.m)), T', decls[0].R))) &&
     wf_init(ctx, decls[1..], defs[1..])))))
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
copredicate wfe_type(ctx: context, T: tp)
{
  wf_type(ctx, T) && exists Ds :: expansion(ctx, 0, T, Ds)
}
copredicate membership(ctx: context, t: tm, l: nat, d: decl)
{
  decl_label(d)==l &&
  forall z:nat :: z !in dom(ctx.m) &&
  exists T :: !tp_fn(z, T) && !tm_fn(z, t) &&
  typing(ctx, t, T) &&
  exists Ds ::
  expansion(ctx, z, T, Ds) &&
  ((Ds.decls_fin? &&
     ((path(t) && exists d' :: d' in Ds.decls && d==decl_subst(z, t, d')) ||
     (!path(t) && d in Ds.decls && !decl_fn(z, d)))) ||
   (Ds.decls_bot? && decl_bot(d)))
}
copredicate field_membership(ctx: context, t: tm, l: nat, T: tp)
{
  exists d :: membership(ctx, t, l, d) &&
  d.decl_tm? && d.l==l && d.T==T
}
copredicate method_membership(ctx: context, t: tm, m: nat, P: tp, R: tp)
{
  exists d :: membership(ctx, t, m, d) &&
  d.decl_mt? && d.m==m && d.P==P && d.R==R
}
copredicate type_membership(ctx: context, t: tm, L: nat, S: tp, U: tp)
{
  exists d :: membership(ctx, t, L, d) &&
  ((d.decl_tp_c? && d.Lc==L && d.Sc==S && d.Uc==U) ||
   (d.decl_tp_a? && d.La==L && d.Sa==S && d.Ua==U))
}
copredicate expansion(ctx: context, z: nat, T: tp, Ds: decls)
  ensures expansion(ctx, z, T, Ds) && Ds.decls_fin? ==> decl_seq_sorted(Ds.decls);
{
  match T
  case tp_rfn(T', z', Ds') =>
    exists DsT :: expansion(ctx, z, T, DsT) &&
    exists rfn_decls :: rfn_decls==decl_seq_sort(lst2seq(decls_subst(z', tm_var(z), Ds'))) &&
    decl_seq_sorted(rfn_decls) &&
    Ds==decls_and(decls_fin(rfn_decls), DsT) &&
    (Ds.decls_fin? ==> decl_seq_sorted(Ds.decls))
  case tp_sel_c(p, L) =>
    exists S, U :: type_membership(ctx, p, L, S, U) && expansion(ctx, z, U, Ds)
  case tp_sel_a(p, L) =>
    exists S, U :: type_membership(ctx, p, L, S, U) && expansion(ctx, z, U, Ds)
  case tp_and(T1, T2) =>
    exists Ds1, Ds2 :: expansion(ctx, z, T1, Ds1) && expansion(ctx, z, T2, Ds2) &&
    Ds==decls_and(Ds1, Ds2) &&
    (Ds.decls_fin? ==> decl_seq_sorted(Ds.decls))
  case tp_or(T1, T2) =>
    exists Ds1, Ds2 :: expansion(ctx, z, T1, Ds1) && expansion(ctx, z, T2, Ds2) &&
    Ds==decls_or(Ds1, Ds2) &&
    (Ds.decls_fin? ==> decl_seq_sorted(Ds.decls))
  case tp_top => Ds==decls_fin([])
  case tp_bot => Ds==decls_bot
}
copredicate subtype(ctx: context, S: tp, T: tp)
{
  false // TODO
}
