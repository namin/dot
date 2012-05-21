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
       wfe_tp (G,s) Tc
    /\ exists args, argsRT = args ^args^ (ref a)
    /\ concrete Tc
    /\ lbl.uniq args
    /\ exists ds, (G, s) |= Tc ~< ds
    /\ (forall l v, lbl.binds l v args -> (value_label l \/ method_label l) /\ (exists d, decls_binds l d ds))
    /\ (exists L L', (forall x, x \notin L -> (forall l d, decls_binds l d ds ->
       (forall S U, d ^d^ x = decl_tp S U -> (ctx_bind (G,s) x Tc) |= S ~<: U) /\
       (forall S U, d ^d^ x = decl_mt S U -> (exists v, lbl.binds l v args /\ (forall y, y \notin L' -> (exists U', (ctx_bind (ctx_bind (G,s) x Tc) y S) |= ((v ^ x) ^ y) ~: U' /\ (ctx_bind (ctx_bind (G,s) x Tc) y S) |= U' ~=: U)))) /\
       (forall V, d ^d^ x = decl_tm V -> (exists v, lbl.binds l v args /\ syn_value(v ^ x) /\ (exists V', (ctx_bind (G,s) x Tc) |= (v ^ x) ~: V' /\ (ctx_bind (G,s) x Tc) |= V' ~=: V))))))).

Notation "G |== s" := (typing_store G s) (at level 68).

Definition ok_env G_s :=
  wf_env G_s /\ (forall x T, binds x T (fst G_s) -> wfe_tp G_s T).

Notation "G_s |= 'ok'" := (ok_env G_s) (at level 69).

Lemma env_weakening_notin_wfe_tp: forall L E S T x t,
  x `notin` L -> ctx_bind E x S |= t ^ x ~: T -> wfe_tp (ctx_bind E x S) T ->
  wfe_tp E T.
Proof. (* TODO *) Admitted.

Lemma ok_env_plus: forall E s x S,
  (E,s) |= ok -> E |== s -> 
  ((x, S) :: E, s) |= ok.
Proof. (* TODO *) Admitted.

Lemma typing_store_plus: forall E s x S,
  (E,s) |= ok -> E |== s ->
  ((x, S) :: E) |== s.
Proof. (* TODO *) Admitted.

Lemma wf_env_gamma_uniq : forall E G P,
  wf_env E -> E = (G,P) -> uniq G.
Proof.
  introv Hwf Heq. gen G.
  induction Hwf. introv Heq. inversion Heq. subst. auto.
  introv Heq. inversion Heq. subst. auto.
Qed.

Lemma wf_store_uniq : forall P,
  wf_store P -> uniq P.
Proof.
  introv Hwf.
  induction Hwf. auto. auto.
Qed.

Lemma wf_env_store_uniq : forall E G P,
  wf_env E -> E = (G,P) -> uniq P.
Proof.
  introv Hwf Heq. gen P.
  inversion Hwf; introv Heq; inversion Heq; subst; apply wf_store_uniq; assumption.
Qed.

Lemma tp_unique : forall E t T T',
  E |= t ~: T -> E |= t ~: T' -> T = T'.
Proof.
  introv HT HT'. dependent induction t; inversion HT; inversion HT'; subst.
  Case "a".
    inversion H8. subst. clear H8. clear H6.
    assert (uniq G). apply wf_env_gamma_uniq with (E:=(G,P)) (P:=P). assumption. reflexivity.
    apply binds_unique with (x:=a) (E:=G); assumption.
  Case "ref".
    inversion H6. subst. clear H6. clear H5.
    assert (uniq P). apply wf_env_store_uniq with (E:=(G,P)) (G:=G). assumption. reflexivity.
    assert ((T, args) = (T', args0)) as Heq. apply binds_unique with (x:=l) (E:=P); assumption.
    inversion Heq. subst. reflexivity.
  Case "new".
    skip.
  Case "sel".
    skip.
  Case "msel".
    skip.
  Case "wid".
    inversion HT'. reflexivity.
Qed.

Lemma tp_regular : forall E s t T,
  (E,s) |= ok -> E |== s ->
  (E,s) |= t ~: T ->
  wfe_tp (E,s) T.
Proof.
  introv Hok Hes H. dependent induction H.
  Case "var".
    inversion Hok as [Hwf_env Hbinds].
    apply (Hbinds x T). simpl. assumption.
  Case "ref".
    inversion Hes as [Hwf_store Hcond].
    apply (proj1 (Hcond a T args H0)).
  Case "wid".
    auto.
  Case "sel".
    assumption.
  Case "msel".
    assumption.
  Case "new".
    pick fresh x.
    assert (wfe_tp (ctx_bind (E,s) x Tc) T') as Hwfe_tp.
      apply H6 with (x:=x). apply notin_union_1 in Fr. assumption.
      simpl. apply ok_env_plus; assumption.
      simpl. apply typing_store_plus; assumption.
      simpl. reflexivity.
    apply env_weakening_notin_wfe_tp with (L:=L) (S:=Tc) (x:=x) (t:=t).
    apply notin_union_1 in Fr. assumption. 
    apply H5. apply notin_union_1 in Fr. assumption.
    assumption.
Qed.

Definition preservation := forall G s t T s' t',
  (G,s) |= ok ->
  G |== s ->
  (G,s) |= t ~: T ->
  s |~ t ~~> t' ~| s' ->
  exists T',
  (G,s') |= t' ~: T' /\
  (G,s') |= T' ~=: T.

(*
Lemma succ_env_stable : forall G s G' s' t t' t'' T,
  G |== s -> G' |== s' -> (G,s) |= t ~: T -> s |~ t' ~~> t'' ~| s' ->
  (G',s') |= t ~: T.
Proof. (* TODO *) Admitted.
*)

Theorem preservation_holds : preservation.
Proof. unfold preservation.
  introv Hok Hc Ht Hr. gen T. induction Hr.
  Case "red_msel".  (* TODO *) skip.
  Case "red_msel_tgt1". (* TODO *) skip.
  Case "red_msel_tgt2". (* TODO *) skip.
  Case "red_sel". (* TODO *) skip.
  Case "red_sel_tgt". (* TODO *) skip.
  Case "red_wid_tgt".
    introv Ht. inversion Ht. subst.
    specialize (IHHr Hok Hc T' H2). inversion IHHr as [Th' IHHr']. inversion IHHr' as [Hc' Hs']. inversion Hs' as [Hs1 Hs2]. subst.
    exists T. splits.
    apply typing_wid with (T':=Th'). assumption.
    apply sub_tp_transitive with (TMid:=T').
    assumption. (* succ stable for subtyping *) skip. apply same_tp_any. apply sub_tp_refl. skip. skip. apply sub_tp_refl. skip. skip. 
  Case "red_new". (* TODO *) skip.
Qed.