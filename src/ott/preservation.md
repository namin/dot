
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

By induction on the derivation of $[[t|s --> t'|s']]$$.

- Case **Red_New**

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

- Case **Red_Sel**

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

    ### Narrowing Lemma ###
	
  	  If
	
	  * $[[G, xi : Ti, s |- ti : W]]$
	
	  * $[[G, xi : Ti, s |- S' <: Ti]]$ (by transitivity of subtyping through $[[S]]$)
	
	  then $\exists [[W']]$ such that
	
	  * $[[G, xi : S', s |- ti : W']]$
	
	  * $[[G, xi : S', s |- W' <: W]]$
	  
	  * If $[[G, xi : Ti, s |- W <: T]]$, then $[[G, xi : S', s |- W' <: T]]$.
	  
    ### Substitution lemma ###
	
	  If
	  
	  * $[[G, xi : S', s |- ti: W']]$
	  
	  * $[[G, s |- v : S']]$
	  
	  then
	  
	  * $[[G, s |- [v/xi] ti : [v/xi] W']]$
	  
	  * If $[[G, xi : S', s |- W' <: T]]$, then $[[G, s |- [v/xi] W' <: T]]$
	  
	The narrowing and substitution lemmas apply. $[[T']] = [v/xi] W'$.
	
- Case **Red_Ctx**

    There are two cases:
	
    1. t1 l t2 | s --> t1' l t2 | s'
	
	2. v1 l t2 | s --> v1 l t2' | s'
	
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
	
	### Membership narrowing lemma ###
	
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
