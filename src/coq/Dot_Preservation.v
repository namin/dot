(** The DOT calculus -- Preservation. *)

Set Implicit Arguments.
Require Import List.
Require Export Dot_Labels.
Require Import Metatheory LibTactics_sf.
Require Export Dot_Syntax Dot_Definitions Dot_Rules Dot_Lemmas Dot_Transitivity.
Require Import Coq.Program.Equality.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Logic.Decidable.

Definition typing_store G s :=
  wf_store s
  /\ (forall a Tc argsRT, binds a (Tc, argsRT) s ->
    exists args, argsRT = args ^args^ (ref a)
    /\ concrete Tc
    /\ lbl.uniq args
    /\ exists ds, (G, s) |= Tc ~< ds
    /\ (forall l v, lbl.binds l v args -> (value_label l \/ method_label l) /\ (exists d, decls_binds l d ds))
    /\ (exists L L', (forall x, x \notin L -> (forall l d, decls_binds l d ds ->
       (forall S U, d ^d^ x = decl_tp S U -> (ctx_bind (G,s) x Tc) |= S ~<: U) /\
       (forall S U, d ^d^ x = decl_mt S U -> (exists v, lbl.binds l v args /\ (forall y, y \notin L' -> (exists U', (ctx_bind (ctx_bind (G,s) x Tc) y S) |= ((v ^ x) ^ y) ~: U' /\ (ctx_bind (ctx_bind (G,s) x Tc) y S) |= U' ~=: U)))) /\
       (forall V, d ^d^ x = decl_tm V -> (exists v, lbl.binds l v args /\ syn_value(v ^ x) /\ (exists V', (ctx_bind (G,s) x Tc) |= (v ^ x) ~: V' /\ (ctx_bind (G,s) x Tc) |= V' ~=: V))))))).

Notation "G |== s" := (typing_store G s) (at level 68).

Definition preservation := forall G s t T s' t',
  G |== s ->
  (G,s) |= t ~: T ->
  s |~ t ~~> t' ~| s' ->
  exists G' T',
  G' |== s' /\
  (G',s') |= t' ~: T' /\
  (G',s') |= T' ~=: T.