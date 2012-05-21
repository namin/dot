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

(*
Lemma succ_env_stable : forall G s G' s' t t' t'' T,
  G |== s -> G' |== s' -> (G,s) |= t ~: T -> s |~ t' ~~> t'' ~| s' ->
  (G',s') |= t ~: T.
Proof. (* TODO *) Admitted.
*)

Theorem preservation_holds : preservation.
Proof. unfold preservation.
  introv Hc Ht Hr. gen T. induction Hr.
  Case "red_msel".  (* TODO *) skip.
  Case "red_msel_tgt1". (* TODO *) skip.
  Case "red_msel_tgt2". (* TODO *) skip.
  Case "red_sel". (* TODO *) skip.
  Case "red_sel_tgt". (* TODO *) skip.
  Case "red_wid_tgt".
    introv Ht. inversion Ht. subst.
    specialize (IHHr Hc T' H2). inversion IHHr as [G' IHHr']. inversion IHHr' as [Te' IHHr'']. inversion IHHr'' as [Hc' IHHr''']. inversion IHHr''' as [Ht' Hs']. inversion Hs'. subst.
    exists G'. exists T. splits.
    assumption.
    apply typing_wid with (T':=Te'). assumption.
    apply sub_tp_transitive with (TMid:=T').
    assumption. (* succ stable for subtyping *) skip. apply same_tp_any. apply sub_tp_refl. skip. skip. apply sub_tp_refl. skip. skip. 
  Case "red_new". (* TODO *) skip.
Qed.