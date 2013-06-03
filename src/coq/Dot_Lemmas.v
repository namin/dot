(** The DOT calculus -- Lemmas *)

Set Implicit Arguments.
Require Import List.
Require Export Dot_Labels.
Require Import Metatheory LibTactics_sf.
Require Export Dot_Syntax Dot_Definitions Dot_Rules.
Require Import Coq.Program.Equality.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Logic.Decidable.

Lemma value_xor_method_label : forall l,
  value_label l -> method_label l -> False.
Proof.
  introv Hvalue Hmethod. inversion Hvalue. inversion Hmethod.
  rewrite <- H0 in H. inversion H.
Qed.

(* ********************************************************************** *)
(** ** Declarations *)

Lemma decls_dom_subset_nil: forall ds,
  decls_dom_subset (decls_fin ds) (decls_fin nil) -> ds = nil.
Proof.
  (* TODO *)
Admitted.
Hint Resolve decls_dom_subset_nil.

Lemma decls_dom_subset_refl: forall DS,
  decls_dom_subset DS DS.
Proof.
  unfold decls_dom_subset. destruct DS. unfold "[<l=]". intros a H. assumption. reflexivity.
Qed.
Hint Resolve decls_dom_subset_refl.

Lemma decls_ok_fin_nil : decls_ok (decls_fin nil).
Proof.
  unfolds decls_ok. split.
    unfolds decls_uniq. introv Hx. inversion Hx; inversion H; subst; auto.
    introv Hbinds. inversion Hbinds; inversion H; inversion H1; subst; inversion H0.
Qed.

Lemma decls_and_exists : forall ds1 ds2,
  decls_ok ds1 -> decls_ok ds2 -> exists dsm, and_decls ds1 ds2 dsm.
Proof.
  (* TODO *)
Admitted.

Lemma decls_or_exists : forall ds1 ds2,
  decls_ok ds1 -> decls_ok ds2 -> exists dsm, or_decls ds1 ds2 dsm.
Proof.
  (* TODO *)
Admitted.

(* ********************************************************************** *)
(** ** Expansion *)

Lemma expansion_decls_ok : forall es E T DS,
  expands es E T DS -> decls_ok DS.
Proof.
  introv H. induction H; try solve [
    apply decls_ok_fin_nil |
    inversion H; assumption |
    inversion H0; assumption |
    inversion H1; assumption].
Qed.
Hint Resolve expansion_decls_ok.

Lemma expands_bot_inf_nil : forall E, E |= tp_bot ~<! decls_inf nil.
Proof.
  Hint Constructors bot_decl valid_label.
  intros E.
  apply expands_bot; auto.
  Case "bot_decls (decls_inf nil)". unfold bot_decls. splits.
    SCase "decls_ok (decls_inf nil)". unfold decls_ok. splits.
      SSCase "decls_uniq (decls_inf nil)". unfold decls_uniq.
        introv H. inversions H; inversions H0; auto.
      SSCase "valid label". introv Hbind.
        inversions Hbind. inversions H. inversions H1. inversions H1. inversions H0.
        inversions H1. inversions H2. auto. inversions H2. inversions H1. auto. inversions H1. auto.
    SCase "binds <-> bot /\ valid". intros l d. splits.
      SSCase "->". intro Hbind.
        inversions Hbind. inversions H. inversions H1. inversions H1. inversions H0. inversions H.
        inversions H1. inversions H. auto. inversions H. inversions H1. auto. inversions H1. auto.
      SSCase "<-". intro H.
        inversions H. apply decls_binds_inf with (dsl:=nil); auto. inversions H0; inversions H1; auto.
Qed.
Hint Resolve expands_bot_inf_nil.

Lemma expansion_exists : forall E T,
  wf_tp E T -> exists DS, E |= T ~<? DS.
Proof.
  introv Hwf. exists (decls_fin nil). apply expands_loose.
Qed.

(* ********************************************************************** *)
(** ** Well-formedness *)

(* ********************************************************************** *)
(** ** Regularity *)

Lemma sub_tp_regular : forall E S T,
  E |= S ~<: T ->
  wf_tp E S /\ wf_tp E T.
Proof.

Hint Extern 1 (wf_tp ?E ?T) =>
  match goal with
  | IH: wf_tp ?E ?T /\ _ |- _ => apply (proj1 IH)
  | IH: _ /\ wf_tp ?E ?T |- _ => apply (proj2 IH)
  end.

Hint Constructors wf_tp expands.

Hint Extern 1 (wf_tp ?E ?T) =>
  match goal with
  | IH: wf_tp ?E ?T |- _ => inversion IH; subst; assumption
  | IH: wf_tp ?E ?T /\ _ |- _ =>
    let Hwf := fresh "Hwf" in (assert (wf_tp E T) as Hwf);
      try apply (proj1 IH); inversion Hwf; assumption
  | IH: _ /\ wf_tp ?E ?T |- _ =>
    let Hwf := fresh "Hwf" in (assert (wf_tp E T) as Hwf);
      try apply (proj2 IH); inversion Hwf; assumption
  end.

  introv H. induction H; splits; eauto 3.
Qed.

(* *********************************************************************** *)
(** * #<a name="auto"></a># Automation *)

Hint Extern 1 (wf_tp ?E ?T) =>
  match goal with
  | H: sub_tp E T _ |- _ => apply (proj1 (sub_tp_regular H))
  | H: sub_tp E _ T |- _ => apply (proj2 (sub_tp_regular H))
  end.

