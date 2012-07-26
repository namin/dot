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


Inductive in_rel_v (s: store) (ls: list label) : tm -> Prop :=
| in_rel_v_ref : forall a Tc ags,
  binds a (Tc, ags) s ->
  (forall l, In l ls -> exists t, lbl.binds l t ags) ->
  in_rel_v s ls (ref a)
.

Inductive red_star : store -> tm -> store -> tm -> Prop :=
| red_star_step  : forall s t s' t', red s t s' t' -> red_star s t s' t'
| red_star_refl  : forall s t, red_star s t s t
| red_star_trans : forall s1 t1 s2 t2 s3 t3,
  red_star s1 t1 s2 t2 ->
  red_star s2 t2 s3 t3 ->
  red_star s1 t1 s3 t3
.

Definition irred (s: store) (t: tm) := ~ (exists s' t', red s t s' t').

Inductive in_rel_t (s: store) (ls: list label) : tm -> Prop :=
| in_rel_t_any : forall t,
  (forall s' t', red_star s t s' t' /\ irred s' t' -> in_rel_v s' ls t') ->
  in_rel_t s ls t
.