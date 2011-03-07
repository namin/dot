Set Implicit Arguments.
Require Import List.
Require Import syntax_binding theory.
Require Import Metatheory LibTactics_sf support.

Lemma sub_decls_pres_binds : forall l D DS E DS' q,
    lbl.binds l D DS -> sub_decls E q DS' DS -> 
      exists D', exists q, lbl.binds l D' DS' /\ sub_decl E q D' D.
Proof. Admitted.

