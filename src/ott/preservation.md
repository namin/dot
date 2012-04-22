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
* $[[G', s' |- T' <: T]]$

Proof Sketch
------------

By induction on the derivation of $[[t|s --> t'|s']]$.

### Case **Red-New** ###

$[[t]] = [[val x = new c; t']]$ where $[[c]] = [[Tc { </ li(xi:Ti) = ti // i /> }]]$.

For $[[G, s |- t : T]]$, only the **Typ-New** rule applies.

We assume $[[x]]$ is fresh, without loss of generality thanks to alpha-conversion.

$[[s']] = [[s, x |-> c]]$

$[[G']] = [[G, x : Tc]]$

By construction, $[[G]] \subseteq [[G']]$ and $[[G' |= s']]$.

Through the **Typ-New** rule, we know that

$[[G',s |- t' : T]]$

so $[[G',s' |- t' : T]]$, since $s \subseteq s'$, and the same derivation is possible.

Thus $T = T'$ and we are done.

### Case **Red-Sel** ###

$[[t]] = [[x li v]]$ where $[[x |-> Tc { </ li(xi:Ti) = ti // i /> } in s]]$.

$s' = s$

$[[t']] = [[ [v/xi] ti ]]$

For $[[G, s |- x li v : T]]$, only the **Typ-Sel** rule applies. Premises:

* $[[G, s |- x mem li : S -> T]]$
* $[[G, s |- v : S']]$
* $[[G, s |- S' <: S]]$
    
By $[[G |= s]]$: $\exists W$, such that

* $[[G, s |- S <: Ti]]$
* $[[G, xi : Ti, s |- ti : W]]$
* $[[G, xi : Ti, s |- W <: T]]$

#### Narrowing Lemma ####

If

* $[[G, xi : Ti, s |- ti : W]]$
* $[[G, xi : Ti, s |- S' <: Ti]]$ (by transitivity of subtyping through $[[S]]$)

then $\exists [[W']]$ such that

* $[[G, xi : S', s |- ti : W']]$
* $[[G, xi : S', s |- W' <: W]]$
* If $[[G, xi : Ti, s |- W <: T]]$, then $[[G, xi : S', s |- W' <: T]]$.
    
#### Substitution lemma ####

If

* $[[G, xi : S', s |- ti: W']]$
* $[[G, s |- v : S']]$

then $\exists [[W'']]$ such that

* $[[G, s |- [v/xi] ti : W'']]$
* $[[G, xi : S', s |- W'' <: W']]$

The narrowing and substitution lemmas apply. $[[T']] = [[W'']]$.
	
### Case **Red-Ctx** ###

There are two cases:

1. $[[t1 l t2 | s --> t1' l t2 | s']]$
2. $[[v1 l t2 | s --> v1 l t2' | s']]$

In both cases, only the **Typ-Sel** rule applies. Premises:

* $[[G, s |- t1 mem l : S1 -> T]]$
* $[[G, s |- t2 : T2]]$
* $[[G, s |- T2 <: S1]]$

For case 2, by induction hypothesis, $\exists [[G']], [[T2']]$
such that $[[G', s' |- t2': T2']]$ and
$[[G', s' |- T2' <: T2]]$. By transitivity of subtyping on
$[[T2]]$ (with strengthening of context),
$[[G', s' |- T2' <: S1]]$. So the **Typ-Sel** rule applies with
the result $[[T']] = [[T]]$.
	
For case 1, by induction hypothesis, $\exists [[G']], [[T1']]$
such that $[[G', s |- t1' : T1']]$ and $[[G', s' |- T1' <: T1]]$
where $[[G,s |- t1 : T1]]$.
    	
#### Membership narrowing lemma ####

If

* $[[G, s |- t1 : T1]]$
* $[[G, s |- t1' : T1']]$
* $[[G, s |- T1' <: T1]]$
* $[[G, s |- t1 mem l : S1 -> T]]$
    
then $\exists [[S1']], [[T']]$ such that

* $[[G, s |- t1' mem l : S1' -> T']]$
* $[[G, s |- l : S1' -> T' <: l : S1 -> T]]$

The narrowing membership lemma and **DSub-Value** and **Typ-Sel**
rules apply, with result $[[T']]$.

Substitution Lemma
==================

Statement
---------

If

* $[[G, x : S, s |- t : T]]$
* $[[G, s |- v : S]]$

then $\exists [[T']]$ such that

* $[[G, s |- [v/x]t : T']]$
* $[[G, x : S, s |- T' <: T]]$

Proof Sketch
------------

By induction on the derivation of $[[G, x : S, s |- t : T]]$.

### Case **Typ-Var** ###

$[[t]] = [[z]]$. Premise: $[[z : T in G, x : S]]$.

If $[[z]] = [[x]]$, then $[[T]] = [[S]] = [[T']]$, since $[[ [v/x] z]]
= [[ [v/x] x]] = [[x]]$. If $[[z]] \not= [[x]]$, then $[[ [v/x] z]] =
[[z]]$, so $[[T]] = [[T']]$.

### Case **Typ-Sel** ###

$[[t]] = [[t1 l t2]]$. Premises:

* $[[G, s |- t1 mem l1 : S1 -> T]]$
* $[[G, s |- t1 : T1]]$
* $[[G, s |- t2 : T2]]$
* $[[G, s |- T2 <: S1]]$

Let $[[ [v/x]t]] = [[t']] = [[t1' l t2']] = [[ [v/x]t1 l [v/x]t2]]$.

By induction hypothesis:

* $[[G, s |- t2 : T2]]$ implies

  * $[[G, s |- t2' : T2']]$
  * $[[G, s |- T2' <: T2']]$

* $[[G, s |- t1 : T1]]$ implies

  * $[[G, s |- t1' : T1']]$
  * $[[G, s |- T1' <: T1']]$

By **membership narrowing lemma**:

* $[[G, s |- t1' mem l : S1' -> T']]$
* $[[G, s |- l : S1' -> T' <: l : S1 -> T]]$

By **declaration subsumption**:

* $[[G, s |- S1 <: S1']]$
* $[[G, s |- T' <: T]]$

By transitivity of subtyping, the **Typ-Sel** rule applies with result $[[T']]$.

### Case **Typ-New** ###

$[[t]] = [[val z = new Tc { </ li(xi:Ti) = ti // i /> }; t0]]$

$[[t']] = [[ [v/x]t]] = [[val z = new [v/x]Tc { </ li(xi:[v/x]Ti) = [v/x]ti // i /> }; [v/x]t0]]$

For the **Typ-New** rule to apply again, we need substitution to
preserve the properties checked by the **Typ-New** rule. In
particular, substitution must preserve good bounds and well-formed and
expanding types.

For well-formed and expanding types, this is not the case, when taking
into account possible narrowing of the type of the substituted
term. This leads to a counterexample to preservation:

$[[
val z0 = new Top { z =>
                   L : Bottom .. Top { z =>
                                       La1: Bottom .. Top,
                                       La2: Bottom .. z.La1
                                     }
                 }
             {};
(app (fun (x: Top { z =>
                    L : Bottom .. Top { z =>
                                        La1: Bottom .. Top,
                                        La2: Bottom .. Top
                                      }
                  }) Top
           val z = new Top { z => l : Bottom -> Top }
                   {l(y : x.L /\ Top { z =>
                                       La1: Bottom .. z.La2,
                                       La2: Bottom .. Top
                                     }
                     ) = (fun (x0: y.La1) Top x0)};
		   (cast Top z))
     z0)
]]$

Narrowing Lemma
===============

Statement
---------

If

* $[[G, x : S, s |- t : T]]$
* $[[G, s |- S' <: S]]$

then $\exists [[T']]$ such that

* $[[G, x : S', s |- t : T']]$
* $[[G, x : S', s |- T' <: T]]$

Proof Sketch
------------

Similar to **substitution lemma**, stuck at **Typ-New**.

Membership Narrowing Lemma
==========================

Statement
---------

If

* $[[G, s |- t : T]]$
* $[[G, s |- t' : T']]$
* $[[G, s |- T' <: T]]$
* $[[G, s |- t mem l : S1 -> T1]]$
* $[[G, s |- T' wfe]]$

then $\exists [[S1']], [[T1']]$ such that

* $[[G, s |- t' mem l : S1' -> T1']]$
* $[[G, s |- l : S1' -> T1' <: l : S1 -> T1]]$

Proof Sketch
------------

Depends on **expansion narrowing lemma**.

Expansion Narrowing Lemma
=========================

Statement
---------

If

* $[[G, s |- T expands z Dseq]]$
* $[[G, s |- T' expands z Dseq']]$
* $[[G, s |- T' <: T]]$

then

* $[[G, z : T', s |- Dseq' <: Dseq]]$

Proof Sketch
------------

By induction on the derivation of $[[G, s |- T' <: T]]$. Todo.

Subtyping Transitivity Narrowing Lemma
======================================

Statement
---------

If

* $[[G, x : S1, s |- T1 <: T2]]$
* $[[G, x : S2, s |- T2 <: T3]]$
* $[[G, s |- S2 <: S1]]$

then

* $[[G, x : S2, s |- T1 <: T3]]$

Proof Sketch
------------

Todo.
