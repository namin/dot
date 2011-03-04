Set Implicit Arguments.
Require Import List.
Require Import syntax_binding theory.
Require Import Metatheory LibTactics_sf support.

Lemma expands_precise_concrete_function : forall E T DS DS',
  concrete T -> E |= T ~< DS @ precise -> E |= T ~< DS' @ precise -> DS = DS'.
Proof. Admitted.

Lemma sub_decls_pres_binds : forall l D DS E DS' q,
    LabelMapImpl.binds l D DS -> sub_decls E q DS' DS -> 
      exists D', exists q, LabelMapImpl.binds l D' DS' /\ sub_decl E q D' D.
Proof. Admitted.

