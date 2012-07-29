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

Fixpoint rel_x (k: nat) (s: store) (a: loc) (T: tp) (DR: decls): Prop :=
  match k with
    | O => DR = decls_fin nil
    | S j =>
      match T with
        | tp_rfn T DS => forall DSP,
          rel_x j s a T DSP ->
          and_decls DSP ((decls_fin DS) ^ds^ (ref a)) DR
        | tp_sel p L => forall a' Tp Dp S U DU,
          path p ->
          type_label L ->
          red_star s (ref a) s (ref a') ->
          rel_v j s a' Tp ->
          rel_x j s a' Tp Dp ->
          decls_binds L (decl_tp S U) Dp ->
          rel_x j s a (U ^tp^ (ref a')) DU ->
          DR = DU ^ds^ (ref a)
        | tp_and T1 T2 => forall DS1 DS2,
          rel_x j s a T1 DS1 ->
          rel_x j s a T2 DS2 ->
          and_decls DS1 DS2 DR
        | tp_or T1 T2 => forall DS1 DS2,
          rel_x j s a T1 DS1 ->
          rel_x j s a T2 DS2 ->
          or_decls DS1 DS2 DR
        | tp_top => DR = decls_fin nil
        | tp_bot => bot_decls DR
      end
  end

with rel_v (k: nat) (s: store) (ta: tm) (T: tp): Prop :=
  match k with
    | O => True
    | S j => forall a DT Tc ags DTc,
      ta = ref a ->
      binds a (Tc, ags) s ->
      lbl.uniq ags ->
      rel_x j s a T DT ->
      (nil,s) |= Tc ~< DTc ->
      (forall l v, lbl.binds l v ags ->
        (value_label l \/ method_label l) /\
        (exists d, decls_binds l d DTc)) /\
      (forall l d', decls_binds l d' DT ->
        exists d, decls_binds l d (DTc ^ds^ (ref a)) /\
          (forall S U, d = decl_tp S U -> True) /\ (* ??? *)
          (forall S U, d = decl_mt S U -> exists t,
            lbl.binds l t ags /\ method_label l /\
            (forall y,
              rel_v j s y S -> rel_e j s (t ^^ y) U)) /\
          (forall V, d = decl_tm V -> exists v,
            lbl.binds l v ags /\ value_label l /\
            rel_v j s v V))
  end

with rel_e (k: nat) (s: store) (t: tm) (T: tp): Prop :=
  match k with
    | O => True
    | S j =>
      forall s' t',
        red_star s t s' t' ->
        irred s' t' ->
        rel_v j s' t' T
  end
.
