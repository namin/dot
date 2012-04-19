
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

* Case **Red_New**

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

* Case **Red_Sel**

* Case **Red_Ctx**
