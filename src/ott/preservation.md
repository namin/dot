Preservation
============

Statement
---------
if 

* $[[G |= s]]$
* $[[G, s |- t : T]]$
* $[[t|s --> t'|s']]$

then $\exists [[G']], [[T']]$ such that

* $[[G]] \subseteq [[G']]$
* $[[G' |= s']]$
* $[[G', s' |- t' : T']]$
* $[[G', s' |- T' == T]]$

Proof Sketch
------------

By induction on the derivation of $[[t|s --> t'|s']]$.

### Case **Red-New** ###

$[[t]] = [[val x = new c; t']]$ where $[[c]] = [[Tc { </ defi // i /> }]]$.

For $[[G, s |- t : T]]$, only the **Typ-New** rule applies.

We assume $[[x]]$ is fresh, without loss of generality thanks to alpha-conversion.

$[[s']] = [[s, x |-> c]]$

$[[G']] = [[G, x : Tc]]$

By construction, $[[G]] \subseteq [[G']]$ and $[[G' |= s']]$.

Through the **Typ-New** rule, we know that

$[[G', s |- t' : T]]$

so $[[G', s' |- t' : T]]$, since $[[s]] \subseteq [[s']]$, and the same derivation is possible.

Thus $[[T]] = [[T']]$ and we are done.

### Case **Red-VSel** ###

$[[t]] = [[v.l]]$ where $[[x |-> Tc { </ defi // i /> } in s]]$,
$[[defi is l=v']]$, $[[v downto x]]$, $[[s |- v.l | v' up_value v'']]$.

$[[G']] = [[G]]$ and $[[s']] = [[s]]$.

$[[t']] = [[v'']]$.

For $[[G, s |- v.l : T]]$, only the **Typ-VSel** rule applies, with
premise: $[[G, s |- v mem l : T]]$.

By $[[G |= s]]$: $\exists [[T']]$, such that

* $[[G, s |- v' : T']]$
* $[[G, s |- T' == T]]$

Because we propagate the widening, $\exists [[T'']]$, such that

* $[[G, s |- v'' : T']]$
* $[[G, s |- T'' == T']]$

### Case **Red-MSel** ###

$[[t]] = [[v m v']]$ where $[[x |-> Tc { </ defi // i /> } in s]]$,
$[[defi is m(xi)=ti]]$, $[[v downto x]]$, $[[s |- v.m(v') | \xi.ti up_method t']]$.

$[[s']] = [[s]]$.

For $[[G, s |- v m v' : T]]$, only the **Typ-MSel** rule applies. Premises:

* $[[G, s |- v mem m : S -> T]]$
* $[[G, s |- v' : S']]$
* $[[G, s |- S' == S]]$
    
By $[[G |= s]]$: $\exists [[W]]$, such that

* $[[G, xi : S, s |- ti : W]]$
* $[[G, xi : S, s |- W == T]]$

Because we propagate the widening, $\exists [[T']]$, such that
* $[[G, s |- t' : T']]$
* $[[G, s |- T' == W]]$

#### $[[==]]$ Lemma ####

If

* $[[G, xi : S, s |- ti : W]]$
* $[[G, xi : S, s |- S' == S]]$

then $\exists [[W']]$ such that

* $[[G, xi : S', s |- ti : W']]$
* $[[G, xi : S', s |- W' == W]]$
* If $[[G, xi : S, s |- W == T]]$, then $[[G, xi : S', s |- W' == T]]$.
    
#### Substitution lemma ####

If

* $[[G, xi : S', s |- ti: W']]$
* $[[G, s |- v' : S']]$

then $\exists [[W'']]$ such that

* $[[G, s |- [v'/xi] ti : W'']]$
* $[[G, xi : S', s |- W'' == W']]$

The $[[==]]$ and substitution lemmas apply. $[[T']] = [[W'']]$.
	
### Case **Red-Ctx** ###

There are four cases:

1. $[[t1.l | s --> t1'.l | s']]$
2. $[[t1 m t2 | s --> t1' m t2 | s']]$
3. $[[v1 m t2 | s --> v1 m t2' | s']]$
4. $[[t1 : T | s --> t1' : T | s']]$

For case 1, only the **Typ-VSel** rule applies, with premise:
$[[G, s |- t1 mem l : T]]$. By induction hypothesis, $\exists [[G']],
[[s']], [[T1']]$ such that $[[G', s' |- t1' : T1']]$ and
$[[G', s' |- T1' == T1]]$ where $[[G, s |- t1 : T1]]$. The conclusion
follows by the membership-$[[==]]$ lemma.

For cases 2 and 3, only the **Typ-Sel** rule applies. Premises:

* $[[G, s |- t1 mem m : S1 -> T]]$
* $[[G, s |- t2 : T2]]$
* $[[G, s |- T2 == S1]]$

For case 3, by induction hypothesis, $\exists [[G']], [[s']], [[T2']]$
such that $[[G', s' |- t2': T2']]$ and $[[G', s' |- T2' == T2]]$. By
transitivity of $[[==]]$ on $[[T2]]$ (with strengthening of context),
$[[G', s' |- T2' == S1]]$. So the **Typ-Sel** rule applies with the
result $[[T']] = [[T]]$.
	
For case 2, by induction hypothesis, $\exists [[G']], [[s']], [[T1']]$
such that $[[G', s' |- t1' : T1']]$ and $[[G', s' |- T1' <: T1]]$
where $[[G, s |- t1 : T1]]$. The conclusion follows by the
membership-$[[==]]$ lemma.

For case 4, only the **Typ-Wid** rule applies with premises:

* $[[G, s |- t1 : T1]]$
* $[[G, s |- T1 <: T]]$

By induction hypothesis, $\exists [[G']], [[s']], [[T1']]$ such that
$[[G', s' |- t1' : T1']]$ and $[[G', s' |- T1' == T1]]$. So,
$[[G', s' |- T1' <: T]]$, and the **Typ-Wid** rule applies again with
result $[[T']] = [[T]]$.

#### Membership-$[[==]]$ lemma ####

If

* $[[G, s |- t1 : T1]]$
* $[[G, s |- t1' : T1']]$
* $[[G, s |- T1' == T1]]$

and if

* $[[G, s |- t1 mem m : S1 -> T]]$
    
then $\exists [[S1']], [[T']]$ such that

* $[[G, s |- t1' mem m : S1' -> T']]$
* $[[G, s |- S1 == S1']]$
* $[[G, s |- T' == T]]$

or if

* $[[G, s |- t1 mem l : T]]$

then $\exists [[T']]$ such that

* $[[G, s |- t1' mem l : T']]$
* $[[G, s |- T' == T]]$

Substitution Lemma
==================

Statement
---------

If

* $[[G, x : S, s |- t : T]]$
* $[[G, s |- v : S]]$

then $\exists [[T']]$ such that

* $[[G, s |- [v/x]t : T']]$
* $[[G, x : S, s |- T' == T]]$

Proof Sketch
------------

By induction on the derivation of $[[G, x : S, s |- t : T]]$.

### Case **Typ-Var** ###

$[[t]] = [[z]]$. Premise: $[[z : T in G, x : S]]$.

If $[[z]] = [[x]]$, then $[[T]] = [[S]] = [[T']]$, since $[[ [v/x] z]]
= [[ [v/x] x]] = [[x]]$. If $[[z]] \not= [[x]]$, then $[[ [v/x] z]] =
[[z]]$, so $[[T]] = [[T']]$.

### Case **Typ-VSel** ###

$[[t]] = [[t1.l]]$ with premises $[[G, s |- t1 mem l : T]]$ and $[[G, x : S, s |- t1 : T1]]$.

Let $[[ [v/x]t]] = [[t']] = [[t1'.l]] = [[ [v/x]t1.l]]$.

By induction hypothesis, $[[G, x : S, s |- t1 : T1]]$ implies
$[[G, s |- t1' : T1']]$ and $[[G, x : S, s |- T1' == T1]]$.

By the **membership-$[[==]]$ lemma**, $[[G, s |- t1' mem l : T']]$ and
$[[G, x : S, s |- T' == T]]$.

The **Typ-VSel** rule applies with result $[[T']]$.

### Case **Typ-MSel** ###

$[[t]] = [[t1 m t2]]$. Premises:

* $[[G, x : S, s |- t1 mem m1 : S1 -> T]]$
* $[[G, x : S, s |- t1 : T1]]$
* $[[G, x : S, s |- t2 : T2]]$
* $[[G, x : S, s |- T2 == S1]]$

Let $[[ [v/x]t]] = [[t']] = [[t1' m t2']] = [[ [v/x]t1 m [v/x]t2]]$.

By induction hypothesis:

* $[[G, x : S, s |- t2 : T2]]$ implies

  * $[[G, s |- t2' : T2']]$
  * $[[G, x : S, s |- T2' == T2]]$

* $[[G, x : S, s |- t1 : T1]]$ implies

  * $[[G, s |- t1' : T1']]$
  * $[[G, x : S, s |- T1' == T1]]$

By the **membership-$[[==]]$ lemma**:

* $[[G, s |- t1' mem m : S1' -> T']]$
* $[[G, x : S, s |- S1 == S1']]$
* $[[G, x : S, s |- T' == T]]$

The **Typ-MSel** rule applies with result $[[T']]$.

### Case **Typ-New** ###

$[[t]] = [[val z = new Tc { </ defi // i /> }; t0]]$

$[[t']] = [[ [v/x]t]] = [[val z = new [v/x]Tc { </ [v/x]defi // i /> }; [v/x]t0]]$

For the **Typ-New** rule to apply again, we need substitution to
preserve the properties checked by the **Typ-New** rule. In
particular, substitution must preserve good bounds and well-formed and
expanding types. We rely on the fact that two $[[==]]$-equivalent
types are indistingushable by judgements.

### Case **Typ-Wid** ###

$[[t]] = [[t1 : T]]$ with premises $[[G, s |- t1 : T1]]$ and
$[[G, s |- T1 <: T]]$.

Let $[[ [v/x]t]] = [[t']] = [[t1' : T']] = [[ [v/x]t1 : [v/x]T]]$.

If $[[x notin fn(T)]]$, then straightforward by induction hypothesis.

Otherwise, is $[[G, x : S, s |- [v/x] T == T]]$? TODO: is this case possible? TODO: then what?

$[[==]]$ Lemma
===============

Statement
---------

If

* $[[G, x : S, s |- t : T]]$
* $[[G, s |- S' == S]]$

then $\exists [[T']]$ such that

* $[[G, x : S', s |- t : T']]$
* $[[G, x : S', s |- T' == T]]$

Proof Sketch
------------

TODO.

Membership-$[[==]]$ Lemma
==========================

Statement
---------

If

* $[[G, s |- t : T]]$
* $[[G, s |- t' : T']]$
* $[[G, s |- T' == T]]$
* $[[G, s |- T' wfe]]$

and if

* $[[G, s |- t mem m : S1 -> T1]]$

then $\exists [[S1']], [[T1']]$ such that

* $[[G, s |- t' mem m : S1' -> T1']]$
* $[[G, s |- S1 == S1']]$
* $[[G, s |- T1' == T1]]$

or if

* $[[G, s |- t mem l : T1]]$

then $\exists [[T1']]$ such that

* $[[G, s |- t' mem l : T1']]$
* $[[G, s |- T1' == T1]]$

Proof Sketch
------------

TODO.

