(** The DOT calculus -- Type Safety via Logical Relations. *)

Set Implicit Arguments.
Require Import List.
Require Export Dot_Labels.
Require Import Metatheory LibTactics_sf.
Require Export Dot_Syntax Dot_Definitions Dot_Rules Dot_Lemmas Dot_Transitivity.
Require Import Coq.Program.Equality.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Logic.Decidable.

Inductive red_star : store -> tm -> store -> tm -> Prop :=
| red_star_none : forall s t, red_star s t s t
| red_star_plus : forall s t s' t' s'' t'',
  red s t s' t' -> red_star s' t' s'' t'' ->
  red_star s t s'' t''
.

Theorem red_star_trans : forall s1 t1 s2 t2 s3 t3,
  red_star s1 t1 s2 t2 -> red_star s2 t2 s3 t3 ->
  red_star s1 t1 s3 t3.
Proof.
  intros s1 t1 s2 t2 s3 t3 H12 H23. gen H23.
  induction H12; intros.
  Case "none".
    assumption.
  Case "plus".
    apply IHred_star in H23.
    apply red_star_plus with (s':=s') (t':=t'); assumption.
Qed.

Definition irred (s: store) (t: tm) := ~ (exists s' t', red s t s' t').

Definition can_step (s: store) (t: tm) := (exists s' t', red s t s' t').

Definition type_safety := forall t T t' s',
  (nil,nil) |= t ~: T -> red_star nil t s' t' ->
  value t' \/ can_step s' t'.



