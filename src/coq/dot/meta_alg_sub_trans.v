Set Implicit Arguments.
Require Import List.
Require Import syntax_binding theory theory_alg.
Require Import Metatheory LibTactics_sf support meta_regular meta_binding meta_weakening meta_narrowing.
Require Import Coq.Program.Equality.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Logic.Decidable.

Definition exposed E p L S U := exists T DS,  path p /\ E |= p ~:! T /\ E |= T ~<! (tp_rfn tp_top DS) /\ lbl.binds L (decl_tp S U) DS.
Hint Unfold exposed.

Definition transitivity_on TMid := forall E T T',  E |= T ~<! TMid -> E |= TMid ~<! T' -> E |= T ~<! T'.
Hint Unfold transitivity_on.

Lemma narrow_sub_decls: forall L E S T DS1 DS2,  
(*  transitivity_on T ->*)
  E |=  S ~<! T ->
  (forall z : atom, z `notin` L ->
     forall_decls (ctx_bind E z T) (DS1 ^ds^ z) (DS2 ^ds^ z) sub_decl_alg) -> 
  (forall z : atom, z `notin` L ->
     forall_decls (ctx_bind E z S) (DS1 ^ds^ z) (DS2 ^ds^ z) sub_decl_alg).
Proof. 
(* TODO *) Admitted.
Hint Resolve narrow_sub_decls.

Lemma sub_tp_alg_trans_tpsel : forall E p T DS l S U T' DS' S' U' Ta Tb,
  path p ->

  E |= p ~:! T ->
  E |= T ~<! tp_rfn tp_top DS ->
  lbl.binds l (decl_tp S U) DS ->

  E |= p ~:! T' ->
  E |= T' ~<! tp_rfn tp_top DS' ->
  lbl.binds l (decl_tp S' U') DS' ->

  E |= Ta ~<! S ^tp^ p ->
  E |= U' ^tp^ p ~<! Tb ->

  E |= Ta ~<! Tb.
Proof.
(* TODO *) Admitted.
Hint Resolve sub_tp_alg_trans_tpsel.

Lemma exposed_u : forall E p L S U x,
  exposed E p L S U -> U ^tp^ p = x -> tp_sel p L = x.
Proof.
(* TODO *) Admitted.
Lemma exposed_s : forall E p L S U x,
  exposed E p L S U -> S ^tp^ p = x -> tp_sel p L = x.
Proof.
(* TODO *) Admitted.

(*

Inspired by sub_transitivity from http://www.chargueraud.org/research/2007/binders/src/Fsub_Soundness.html

Coq provides "dependent induction" to perform "Induction/inversion principle"; 4.2.1. of
http://www.msr-inria.inria.fr/~gares/jar09.pdf explains the latter is needed to perform a proof like this

*)

Lemma sub_tp_alg_trans : forall TMid, transitivity_on TMid.
Proof.
  Hint Constructors sub_tp_alg.
  introv HSubL HSubR. gen E T T'. gen_eq TMid as TMid' eq. gen TMid' eq. 
  induction TMid; intros; gen T';
    induction HSubL; try discriminate; inversions eq; intros; 
      generalize_eqs_vars HSubR; induction HSubR; simplify_dep_elim; subst; auto; try solve [ 
        eapply sub_tp_alg_rfn_r; eauto 2; eapply narrow_sub_decls; eauto 2 |
        eapply sub_tp_alg_and_r; eauto 2 | 
        eapply sub_tp_alg_and_l1; eapply IHHSubL; eauto 2 |
        eapply sub_tp_alg_and_l2; eapply IHHSubL; eauto 2 |
        eapply sub_tp_alg_rfn_l; eapply IHHSubL; eauto 2 |
        eapply sub_tp_alg_tpsel_l; eauto 3 using sub_tp_alg_rfn_r |
        eapply sub_tp_alg_tpsel_r; eauto 3 using sub_tp_alg_rfn_l |
        eapply sub_tp_alg_or_l; eauto 3 using IHHSubL1, sub_tp_alg_tpsel_l, IHHSubL2 |
        eapply sub_tp_alg_rfn_r; eauto 3 using IHHSubR1, narrow_sub_decls, sub_tp_alg_rfn_r, IHHSubR2 |
        eapply sub_tp_alg_fun; eauto 2 using IHTMid1, IHTMid2 |
        match goal with
          | [ H1 : ?BX = ?BU ^tp^ ?BPath, H2 : lbl.binds ?BL (decl_tp ?BS ?BU) ?BDS, H3 : ?BE |= ?BPath ~:! ?BT |- _ ] => rewrite exposed_u with (E:=BE) (S:=BS) (U:=BU) (x:=BX); eauto 3; unfold exposed; exists BT BDS; eauto; eauto
          | [ H1 : ?BU ^tp^ ?BPath = ?BX , H2 : lbl.binds ?BL (decl_tp ?BS ?BU) ?BDS, H3 : ?BE |= ?BPath ~:! ?BT |- _ ] => rewrite exposed_u with (E:=BE) (S:=BS) (U:=BU) (x:=BX); eauto 3; unfold exposed; exists BT BDS; eauto; eauto
          | [ H1 : ?BX = ?BS ^tp^ ?BPath, H2 : lbl.binds ?BL (decl_tp ?BS ?BU) ?BDS, H3 : ?BE |= ?BPath ~:! ?BT |- _ ] => rewrite exposed_s with (E:=BE) (S:=BS) (U:=BU) (x:=BX); eauto 3; unfold exposed; exists BT BDS; eauto; eauto
          | [ H1 : ?BS ^tp^ ?BPath = ?BX , H2 : lbl.binds ?BL (decl_tp ?BS ?BU) ?BDS, H3 : ?BE |= ?BPath ~:! ?BT |- _ ] => rewrite exposed_s with (E:=BE) (S:=BS) (U:=BU) (x:=BX); eauto 3; unfold exposed; exists BT BDS; eauto; eauto
        end |
        rewrite <- x; eauto 3 |
        eauto 3]. (* < 5 minutes *)
Qed.
