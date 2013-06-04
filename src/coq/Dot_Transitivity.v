(** The DOT calculus -- Transitivity. *)

Set Implicit Arguments.
Require Import List.
Require Export Dot_Labels.
Require Import Metatheory LibTactics_sf.
Require Export Dot_Syntax Dot_Definitions Dot_Rules Dot_Lemmas.
Require Import Coq.Program.Equality.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Logic.Decidable.

(* ********************************************************************** *)
(** ** Transitivity of Subtyping *)

Definition transitivity_on TMid := forall E T T',
  E |= T ~<: TMid -> E |= TMid ~<: T' -> E |= T ~<: T'.
Hint Unfold transitivity_on.

Hint Constructors sub_tp mem expands.

Theorem sub_tp_transitive : forall TMid, transitivity_on TMid.
Proof.

  introv HSubL HSubR.
  gen T T'. gen_eq TMid as TMid' eq. gen TMid' eq.
  induction TMid; intros;
    dependent induction HSubL; intros;
      dependent induction HSubR; subst; auto; try solve [
        eapply sub_tp_and_r; eauto 2 |
        eapply sub_tp_and_l1; try eapply IHHSubL; eauto 3 |
        eapply sub_tp_and_l2; try eapply IHHSubL; eauto 3 |
        eapply sub_tp_tsel_l; eauto 3 using sub_tp_rfn_r |
        eapply sub_tp_or_l; eauto 3 using IHHSubL1, sub_tp_tsel_l, IHHSubL2 |
        eapply sub_tp_fun; eauto 2 using IHTMid1, IHTMid2 |
        eapply sub_tp_rfn_l; eauto 3 using IHHSubR1, sub_tp_tsel_r, IHHSubR2 |
        eapply sub_tp_rfn_l; eauto 3 using IHHSubL, sub_tp_rfn_r |
        inversions eq |
        eauto 4].

skip.
skip.
skip.
skip.
skip.
skip.
skip.
skip.
skip.
skip.
skip. (* TODO *)

Qed.