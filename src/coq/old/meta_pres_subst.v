Set Implicit Arguments.
Require Import List.
Require Import Metatheory LibTactics_sf support.
Require Import syntax_binding theory.

Lemma subst_pres_typing : forall E x Tx t T v, 
  (exists q, ctx_bind E x Tx |= t ^^ x ~: T ^tp^ x @ q)
  -> value v 
  -> (exists q, E |= v ~: Tx @ q)
  -> exists q, E |= (t ^^ v) ~: (T ^tp^ v) @ q.
Proof. Admitted.