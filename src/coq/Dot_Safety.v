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

Fixpoint rel_v (n: nat) (s: store) (t: tm) (T: tp): Prop :=
  match n, t with
    | O, ref a => a `in` dom s
    | S j, ref a => forall Tc ags DT,
      binds a (Tc, ags) s ->
      lbl.uniq ags ->
      rel_x j s a T DT ->
      (forall l d, decls_binds l d DT ->
        (method_label l -> exists S U t,
          d = decl_mt S U /\ lbl.binds l t ags /\
          (forall y,
            rel_v j s y S -> rel_e j s (t ^^y) U)) /\
        (value_label l -> exists V v,
          d = decl_tm V /\ lbl.binds l v ags /\
          rel_v j s v V))
    | _, _ => False
  end

with rel_e (n: nat) (s: store) (t: tm) (T: tp): Prop :=
  match n with
    | O => True
    | S j =>
      forall s' t',
        red_star s t s' t' ->
        irred s' t' ->
        rel_v j s' t' T
  end

with rel_x (n: nat) (s: store) (a: loc) (TR: tp) (DR: decls): Prop :=
  match n with
    | O => DR = decls_fin nil
    | S j =>
      match TR with
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
          DR = (DU ^ds^ (ref a))
        | tp_and T1 T2 => forall DS1 DS2,
          rel_x j s a T1 DS1 ->
          rel_x j  s a T2 DS2 ->
          and_decls DS1 DS2 DR
        | tp_or T1 T2 => forall DS1 DS2,
          rel_x j s a T1 DS1 ->
          rel_x j s a T2 DS2 ->
          or_decls DS1 DS2 DR
        | tp_top => DR = decls_fin nil
        | tp_bot => bot_decls DR
      end
  end.

Inductive rel_x_cases : nat -> store -> loc -> tp -> decls -> Prop :=
| rel_x_0 : forall s a T,
  rel_x_cases 0 s a T (decls_fin nil)
| rel_x_rfn : forall k s a T DR DS DSP,
  rel_x k s a T DSP ->
  and_decls DSP ((decls_fin DS) ^ds^ (ref a)) DR ->
  rel_x_cases (k+1) s a (tp_rfn T DS) DR
| rel_x_tsel : forall k s a p L a' Tp Dp S U DU,
  path p ->
  type_label L ->
  red_star s (ref a) s (ref a') ->
  rel_v k s a' Tp ->
  rel_x k s a' Tp Dp ->
  decls_binds L (decl_tp S U) Dp ->
  rel_x k s a (U ^tp^ (ref a')) DU ->
  rel_x_cases (k+1) s a (tp_sel p L) (DU ^ds^ (ref a))
| rel_x_and : forall k s a DR T1 T2 DS1 DS2,
  rel_x k s a T1 DS1 ->
  rel_x k s a T2 DS2 ->
  and_decls DS1 DS2 DR ->
  rel_x_cases (k+1) s a (tp_and T1 T2) DR
| rel_x_or : forall k s a DR T1 T2 DS1 DS2,
  rel_x k s a T1 DS1 ->
  rel_x k s a T2 DS2 ->
  or_decls DS1 DS2 DR ->
  rel_x_cases (k+1) s a (tp_or T1 T2) DR
| tp_top : forall k s a,
  rel_x_cases (k+1) s a tp_top (decls_fin nil)
| tp_bot : forall k s a DR,
  bot_decls DR ->
  rel_x_cases (k+1) s a tp_bot DR

with rel_v_cases : nat -> store -> tm -> tp -> Prop :=
| rel_v_0 : forall s a T,
  a `in` dom s ->
  rel_v_cases 0 s (ref a) T
| rel_v_loc : forall k s a T DT Tc ags,
  binds a (Tc, ags) s ->
  lbl.uniq ags ->
  rel_x k s a T DT ->
  (forall l d, decls_binds l d DT ->
    (method_label l -> exists S U t,
      d = decl_mt S U /\ lbl.binds l t ags /\
      (forall y,
        rel_v k s y S -> rel_e k s (t ^^y) U)) /\
    (value_label l -> exists V v,
      d = decl_tm V /\ lbl.binds l v ags /\
      rel_v k s v V)) ->
  rel_v_cases (k+1) s (ref a) T

with rel_e_cases : nat -> store -> tm -> tp -> Prop :=
| rel_e_0 : forall s t T,
  rel_e_cases 0 s t T
| rel_e_k : forall k s t T s' t',
  red_star s t s' t' ->
  irred s' t' ->
  rel_v k s' t' T ->
  rel_e_cases (k+1) s t T
.

Lemma rel_v_def:
  forall k s t T,
    rel_v k s t T <-> rel_v_cases k s t T.
Proof.
(* TODO *) Admitted.

Lemma rval_decr:
  forall k1 k2 s t T,
    rel_v k1 s t T -> k2 <= k1 -> rel_v k2 s t T.
Proof.
(* TODO *) Admitted.