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

Inductive rel_g : nat -> env -> store -> env -> Prop :=
| rel_g_base : forall k E s, dom E = dom s -> rel_g k E s E
| rel_g_cons : forall k E E' s a Tc ags,
  rel_g k E s E' ->
  a `notin` dom s ->
  rel_g k E ((a ~ (Tc, ags)) ++ s) ((a ~ Tc) ++ E')
.

Inductive rel_s : (env -> store -> tm -> tp -> Prop) -> env -> store -> store -> Prop :=
| rel_s_base : forall P E s, dom E = dom s -> rel_s P E s s
| rel_s_cons : forall P E s s' a T c,
  rel_s P E s s' ->
  a `notin` dom E ->
  P ((a ~ T) ++ E) ((a ~ c) ++ s') (fvar a) T ->
  rel_s P ((a ~ T) ++ E) s ((a ~ c) ++ s')
.

Program Fixpoint rel_comp (rt: rel_comp_type) (k: nat) (E: env) (s: store) (t: tm) (T: tp) {measure k}: Prop :=
  match rt, t, k with
    | rel_comp_v, fvar a, _ =>
      wfe_tp E T ->
      a `in` dom s /\
      (forall j Tc ags Ds L,
        j < k ->
        binds a (Tc, ags) s ->
        E |= T ~< Ds ->
          (forall l d, decls_binds l d Ds ->
            (forall S U, d ^d^ (fvar a) = decl_mt S U ->
              exists m, lbl.binds l m ags /\
                (forall y, y `notin` L -> rel_comp rel_comp_e j (ctx_bind E y S) s (m ^ y) U))
            /\
            (forall V, d ^d^ (fvar a) = decl_tm V ->
              exists v, lbl.binds l v ags /\
                rel_comp rel_comp_v j E s v V)))
    | rel_e, _, O => wfe_tp E T
    | rel_e, _, _ =>
      wfe_tp E T /\
      forall i j t' s' s'' E',
        0 < k ->
        i < k ->
        j <= k ->
        rel_s (fun E s t T => rel_comp rel_comp_v i E s t T) E s s' ->
        red_n j s' t s'' t' ->
        irred s'' t' ->
        rel_g k E s'' E' ->
        rel_comp rel_comp_v (k-j-1) E' s'' t' T
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
intros. unfold not. intros. inversion H. inversion H1. inversion H2.
Defined.

Inductive rel_v : nat -> env -> store -> tm -> tp -> Prop :=
| rel_v_fvar : forall k E s T a,
  wfe_tp E T ->
  a `in` dom s ->
  (forall j Tc ags Ds L,
    j < k ->
    binds a (Tc, ags) s ->
    E |= T ~< Ds ->
      (forall l d, decls_binds l d Ds ->
        (forall S U, d ^d^ (fvar a) = decl_mt S U ->
          exists m, lbl.binds l m ags /\
            (forall y, y `notin` L -> rel_comp rel_comp_e j (ctx_bind E y S) s (m ^ y) U))
        /\
        (forall V, d ^d^ (fvar a) = decl_tm V ->
          exists v, lbl.binds l v ags /\
            rel_comp rel_comp_v j E s v V))) ->
  rel_v k E s (fvar a) T
.

Inductive rel_e : nat -> env -> store -> tm -> tp -> Prop :=
| rel_e_0 : forall E s t T,
  wfe_tp E T ->
  rel_e 0 E s t T
| rel_e_e : forall k E s t T i j t' s' s'' E',
  wfe_tp E T ->
  0 < k ->
  i < k ->
  j <= k ->
  rel_s (fun E s t T => rel_v i E s t T) E s s' ->
  red_n j s' t s'' t' ->
  irred s'' t' ->
  rel_g k E s'' E' ->
  rel_v (k-j-1) E' s'' t' T ->
  rel_e k E s t T
.

Definition rel_safe (E: env) (t: tm) (T: tp): Prop :=
  forall k, rel_e k E nil t T.

Theorem rel_e_comp : forall k E s t T,
  rel_comp rel_comp_e k E s t T <-> rel_e k E s t T.
Proof. Admitted.

Theorem rel_v_comp : forall k E s t T,
  rel_comp rel_comp_v k E s t T <-> rel_v k E s t T.
Proof. Admitted.

Theorem rel_fund: forall E t T,
  E |= t ~: T -> rel_safe E t T.
Proof.
  unfold rel_safe.
  intros E t T H k. induction H.
  Case "var".
   skip.
  Case "sel".
   skip.
  Case "msel".
   skip.
  Case "new".
   skip.
Qed.
