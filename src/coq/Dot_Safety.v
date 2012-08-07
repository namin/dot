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

Inductive red_n : nat -> store -> tm -> store -> tm -> Prop :=
| red_n_zero : forall s t, red_n O s t s t
| red_n_plus : forall k s t s' t' s'' t'',
  red s t s' t' -> red_n k s' t' s'' t'' ->
  red_n (S k) s t s'' t''
.

Theorem red_n_trans : forall i j s1 t1 s2 t2 s3 t3,
  red_n i s1 t1 s2 t2 -> red_n j s2 t2 s3 t3 ->
  red_n (i+j) s1 t1 s3 t3.
Proof.
  intros i j s1 t1 s2 t2 s3 t3 H12 H23. gen H23.
  induction H12; intros.
  Case "zero".
    assumption.
  Case "plus".
    apply IHred_n in H23.
    apply red_n_plus with (s':=s') (t':=t'); assumption.
Qed.

Definition irred (s: store) (t: tm) := ~ (exists s' t', red s t s' t').

Definition can_step (s: store) (t: tm) := (exists s' t', red s t s' t').

Definition type_safety := forall k t T t' s',
  nil |= t ~: T -> red_n k nil t s' t' ->
  value t' \/ can_step s' t'.

Inductive rel_comp_type: Type :=
| rel_comp_v
| rel_comp_e
.

(*
Inductive rel_g (P: env -> tm -> tp -> Prop) : ctx -> store -> tm -> store -> tm -> Prop :=
| rel_g_nil: forall s t, rel_g P nil s t s t
| rel_g_cons: forall x T G s t s' t' a Tc ags s'',
  a `notin` dom s ->
  s'' = (a ~ (Tc, ags)) ++ s ->
  P (G,s'') (fvar a) T ->
  rel_g P G s'' (subst_tm x t (fvar a)) s' t' ->
  rel_g P ((x ~ T) ++ G) s t s' t'
.

Program Fixpoint rel_comp (rt: rel_comp_type) (k: nat) (E: env) (t: tm) (T: tp) {measure k}: Prop :=
  match rt, t, k with
    | _, ref a, _ =>
      wfe_tp E T ->
      forall G s,
        (G,s) = E ->
        a `in` dom s /\
        (forall j Tc ags Ds L,
          j < k ->
          binds a (Tc, ags) s ->
          lbl.uniq ags ->
          E |= T ~< Ds ->
          (forall l d, decls_binds l d Ds ->
            (forall S U, d ^d^ (ref a) = decl_mt S U ->
              exists m, lbl.binds l m ags /\
                (forall y, y `notin` L -> rel_comp rel_comp_e j (ctx_bind E y S) (m ^ y) U))
            /\
            (forall V, d ^d^ (ref a) = decl_tm V ->
              exists v, lbl.binds l v ags /\
                rel_comp rel_comp_v j E v V)))
    | rel_e, _, O => True
    | rel_e, _, _ =>
      forall G s t' s' t'' s'' i j,
        (G,s) = E ->
        0 < k ->
        i < k ->
        j <= k ->
        rel_g (fun E t T => rel_comp rel_comp_v i E t T) G s t s' t' ->
        red_n j s' t' s'' t'' ->
        irred s'' t'' ->
        rel_comp rel_comp_v (k-j-1) (G,s'') t'' T
  end
.

Next Obligation of rel_comp_func.
omega.
Defined.

Next Obligation of rel_comp_func.
split.
intros. unfold not. intros. inversion H. inversion H1. inversion H3.
intros. unfold not. intros. inversion H. inversion H0.
Defined.

Next Obligation of rel_comp_func.
split.
intros. unfold not. intros. inversion H. inversion H1. inversion H3.
intros. unfold not. intros. inversion H. inversion H0.
Defined.

Next Obligation of rel_comp_func.
split.
intros. unfold not. intros. inversion H. inversion H1. inversion H3.
intros. unfold not. intros. inversion H. inversion H0.
Defined.

Next Obligation of rel_comp_func.
split.
intros. unfold not. intros. inversion H. inversion H1. inversion H3.
intros. unfold not. intros. inversion H. inversion H0.
Defined.

Next Obligation of rel_comp_func.
split.
intros. unfold not. intros. inversion H. inversion H1. inversion H3.
intros. unfold not. intros. inversion H. inversion H0.
Defined.

Inductive rel_v: nat -> env -> tm -> tp -> Prop :=
| rel_v_ref : forall a k E T,
  wfe_tp E T ->
  forall G s,
    (G,s) = E ->
    a `in` dom s /\
    (forall j Tc ags Ds L,
      j < k ->
      binds a (Tc, ags) s ->
      lbl.uniq ags ->
      E |= T ~< Ds ->
      (forall l d, decls_binds l d Ds ->
        (forall S U, d ^d^ (ref a) = decl_mt S U ->
          exists m, lbl.binds l m ags /\
            (forall y, y `notin` L -> rel_comp rel_comp_e j (ctx_bind E y S) (m ^ y) U))
        /\
        (forall V, d ^d^ (ref a) = decl_tm V ->
          exists v, lbl.binds l v ags /\
            rel_comp rel_comp_v j E v V))) ->
    rel_v k E (ref a) T
.

Inductive rel_e: nat -> env -> tm -> tp -> Prop :=
| rel_e_v : forall k E t T, rel_v k E t T -> rel_e k E t T
| rel_e_0 : forall E t T, rel_e 0 E t T
| rel_e_e : forall k E t T G s t' s' t'' s'' i j,
  (G,s) = E ->
  0 < k ->
  i < k ->
  j <= k ->
  rel_g (fun E t T => rel_v i E t T) G s t s' t' ->
  red_n j s' t' s'' t'' ->
  irred s'' t'' ->
  rel_v (k-j-1) (G,s'') t'' T ->
  rel_e k E t T
.

Definition rel_safe (E: env) (t: tm) (T: tp): Prop :=
  forall k, rel_e k E t T.

Theorem rel_e_comp : forall k E t T,
  rel_comp rel_comp_e k E t T <-> rel_e k E t T.
Proof. Admitted.

Theorem rel_v_comp : forall k E t T,
  rel_comp rel_comp_v k E t T <-> rel_v k E t T.
Proof. Admitted.

Theorem rel_fund: forall E t T,
  E |= t ~: T -> rel_safe E t T.
Proof.
  unfold rel_safe.
  intros E t T H k. induction H.
  Case "var".
    destruct k.
    apply rel_e_0.

    skip.
  Case "ref".
   apply rel_e_v. apply rel_v_ref with (G:=G) (s:=P).
   skip.
   reflexivity.
   skip.
  Case "sel".
   skip.
  Case "msel".
   skip.
  Case "new".
   skip.
Qed.
*)