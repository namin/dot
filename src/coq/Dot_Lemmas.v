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

Lemma expansion_decls_ok : forall E T DS,
  expands E T DS -> decls_ok DS.
Proof.
  introv H. induction H; try solve [
    apply decls_ok_fin_nil |
    inversion H0; assumption |
    inversion H1; assumption].
Qed.
Hint Resolve expansion_decls_ok.

Lemma expands_bot_inf_nil : forall E, wf_env E -> E |= tp_bot ~< decls_inf nil.
Proof.
  Hint Constructors bot_decl valid_label.
  introv Henv.
  apply expands_bot; auto.
  Case "bot_decls (decls_inf nil)". unfold bot_decls. splits.
    SCase "decls_ok (decls_inf nil)". unfold decls_ok. splits.
      SSCase "decls_uniq (decls_inf nil)". unfold decls_uniq.
        introv H. inversions H; inversions H0; auto.
      SSCase "valid label". introv Hbind.
        inversions Hbind; inversions H; inversion H1; subst; try inversions H0; inversions H; subst; auto.
    SCase "binds <-> bot /\ valid". intros l d. splits.
      SSCase "->". intro Hbind.
        inversions Hbind; inversions H; inversion H1; subst; try inversions H0; inversions H; subst; auto.
      SSCase "<-". intro H.
        inversions H. apply decls_binds_inf with (dsl:=nil); auto. inversions H0; inversions H1; auto.
Qed.
Hint Resolve expands_bot_inf_nil.

(* ********************************************************************** *)
(** ** Well-formedness *)

Lemma wfe_bot : forall E, wf_env E -> wfe_tp E tp_bot.
Proof.
  Hint Constructors bot_decl.
  introv Henv.
  apply wfe_any with (DT:=decls_inf nil); auto using wf_bot.
Qed.
Hint Resolve wfe_bot.

Lemma wfe_top : forall E, wf_env E -> wfe_tp E tp_top.
Proof.
  introv Henv.
  apply wfe_any with (DT:=decls_fin nil); auto using wf_top, expands_top.
Qed.
Hint Resolve wfe_top.

(* ********************************************************************** *)
(** ** Regularity *)

Lemma sub_tp_regular : forall E S T,
  E |= S ~<: T ->
  wf_env E /\ wfe_tp E S /\ wfe_tp E T.
Proof.
  introv H. induction H.
  Case "refl". auto.
  Case "fun".
    inversion IHsub_tp1 as [Henv IHsub_tp1'].
    inversion IHsub_tp1' as [HeT1 HeS1].
    inversion IHsub_tp2 as [Henv2 IHsub_tp2'].
    inversion IHsub_tp2' as [HeS2 HeT2].
    splits; try solve [
      assumption |
      apply wfe_any with (DT:=decls_fin nil); try (apply wf_fun; assumption); try (apply expands_fun; assumption)
    ].
  Case "rfn_r".
    inversion IHsub_tp as [Henv IHsub_tp'].
    inversion IHsub_tp' as [HeS HeT].
    splits; try assumption.
  Case "rfn_l".
    inversion IHsub_tp as [Henv IHsub_tp'].
    inversion IHsub_tp' as [HeS HeT].
    splits; try assumption.
  Case "tsel_r".
    inversion IHsub_tp1 as [Henv IHsub_tp1'].
    inversion IHsub_tp1' as [HeS HeU].
    inversion IHsub_tp2 as [Henv_ IHsub_tp2'].
    inversion IHsub_tp2' as [HeS' HeS_].
    splits; try assumption.
    inversion HeU. subst. rename DT into DU. rename H4 into HwU. rename H5 into HxU.
    apply wfe_any with (DT:=DU); try assumption.
    apply wf_tsel_1 with (S:=S) (U:=U); try assumption.
    apply expands_tsel with (S:=S) (U:=U); try assumption.
  Case "tsel_l".
    inversion IHsub_tp1 as [Henv IHsub_tp1'].
    inversion IHsub_tp1' as [HeS HeU].
    inversion IHsub_tp2 as [Henv_ IHsub_tp2'].
    inversion IHsub_tp2' as [HeU_ HeU'].
    splits; try assumption.
    inversion HeU. subst. rename DT into DU. rename H4 into HwU. rename H5 into HxU.
    apply wfe_any with (DT:=DU); try assumption.
    apply wf_tsel_1 with (S:=S) (U:=U); try assumption.
    apply expands_tsel with (S:=S) (U:=U); try assumption.
  Case "and_r".
    inversion IHsub_tp1 as [Henv IHsub_tp1'].
    inversion IHsub_tp1' as [HeT HeT1].
    inversion IHsub_tp2 as [Henv_ IHsub_tp2'].
    inversion IHsub_tp2' as [HeT_ HeT2].
    splits; try assumption.
    inversion HeT1. subst. rename DT into DT1. rename H1 into HwT1. rename H2 into HxT1.
    inversion HeT2. subst. rename DT into DT2. rename H1 into HwT2. rename H2 into HxT2.
    assert (exists DSM, and_decls DT1 DT2 DSM) as Hdsm'. apply decls_and_exists; eauto 3.
    inversion Hdsm' as [DSM Hdsm].
    apply wfe_any with (DT:=DSM); auto.
    apply wf_and; try assumption.
    apply expands_and with (DS1:=DT1) (DS2:=DT2); try assumption.
  Case "and_l1".
    inversion IHsub_tp as [Henv IHsub_tp'].
    inversion IHsub_tp' as [HeT1 HeT].
    inversion HeT. subst. rename H2 into HwT. rename H3 into HxT.
    inversion H0. subst. rename DT0 into DT2. rename H2 into HwT2. rename H3 into HxT2.
    inversion HeT1. subst. rename DT0 into DT1. rename H2 into HwT1. rename H3 into HxT1.
    splits; try assumption.
    assert (exists DSM, and_decls DT1 DT2 DSM) as Hdsm'. apply decls_and_exists; eauto 3.
    inversion Hdsm' as [DSM Hdsm].
    apply wfe_any with (DT:=DSM); try assumption.
    apply wf_and; try assumption.
    apply expands_and with (DS1:=DT1) (DS2:=DT2); try assumption.
  Case "and_l2".
    inversion IHsub_tp as [Henv IHsub_tp'].
    inversion IHsub_tp' as [HeT2 HeT].
    inversion HeT. subst. rename H2 into HwT. rename H3 into HxT.
    inversion H0. subst. rename DT0 into DT1. rename H2 into HwT1. rename H3 into HxT1.
    inversion HeT2. subst. rename DT0 into DT2. rename H2 into HwT2. rename H3 into HxT2.
    splits; try assumption.
    assert (exists DSM, and_decls DT1 DT2 DSM) as Hdsm'. apply decls_and_exists; eauto 3.
    inversion Hdsm' as [DSM Hdsm].
    apply wfe_any with (DT:=DSM); try assumption.
    apply wf_and; try assumption.
    apply expands_and with (DS1:=DT1) (DS2:=DT2); try assumption.
  Case "or_r1".
    inversion IHsub_tp as [Henv IHsub_tp'].
    inversion IHsub_tp' as [HeT HeT1].
    inversion HeT. subst. rename H2 into HwT. rename H3 into HxT.
    inversion H0. subst. rename DT0 into DT2. rename H2 into HwT2. rename H3 into HxT2.
    inversion HeT1. subst. rename DT0 into DT1. rename H2 into HwT1. rename H3 into HxT1.
    splits; try assumption.
    assert (exists DSM, or_decls DT1 DT2 DSM) as Hdsm'. apply decls_or_exists; eauto 3.
    inversion Hdsm' as [DSM Hdsm].
    apply wfe_any with (DT:=DSM); try assumption.
    apply wf_or; try assumption.
    apply expands_or with (DS1:=DT1) (DS2:=DT2); try assumption.
  Case "or_r2".
    inversion IHsub_tp as [Henv IHsub_tp'].
    inversion IHsub_tp' as [HeT HeT2].
    inversion HeT. subst. rename H2 into HwT. rename H3 into HxT.
    inversion H0. subst. rename DT0 into DT1. rename H2 into HwT1. rename H3 into HxT1.
    inversion HeT2. subst. rename DT0 into DT2. rename H2 into HwT2. rename H3 into HxT2.
    splits; try assumption.
    assert (exists DSM, or_decls DT1 DT2 DSM) as Hdsm'. apply decls_or_exists; eauto 3.
    inversion Hdsm' as [DSM Hdsm].
    apply wfe_any with (DT:=DSM); try assumption.
    apply wf_or; try assumption.
    apply expands_or with (DS1:=DT1) (DS2:=DT2); try assumption.
  Case "or_l".
    inversion IHsub_tp1 as [Henv IHsub_tp1'].
    inversion IHsub_tp1' as [HeT1 HeT].
    inversion IHsub_tp2 as [Henv_ IHsub_tp2'].
    inversion IHsub_tp2' as [HeT2 HeT_].
    splits; try assumption.
    inversion HeT1. subst. rename DT into DT1. rename H1 into HwT1. rename H2 into HxT1.
    inversion HeT2. subst. rename DT into DT2. rename H1 into HwT2. rename H2 into HxT2.
    assert (exists DSM, or_decls DT1 DT2 DSM) as Hdsm'. apply decls_or_exists; eauto 3.
    inversion Hdsm' as [DSM Hdsm].
    apply wfe_any with (DT:=DSM); auto.
    apply wf_or; try assumption.
    apply expands_or with (DS1:=DT1) (DS2:=DT2); try assumption.
  Case "top".
    splits; try assumption.
    apply wfe_any with (DT:=decls_fin nil).
    apply wf_top.
    apply expands_top.
    assumption.
  Case "bot".
    splits; try assumption.
    apply wfe_any with (DT:=decls_inf nil).
    apply wf_bot.
    apply expands_bot_inf_nil.
    assumption.
Qed.

(* *********************************************************************** *)
(** * #<a name="auto"></a># Automation *)
    
Hint Extern 1 (wf_env ?E) =>
  match goal with
  | H: sub_tp _ _ _ |- _ => apply (proj1 (sub_tp_regular H))
  end.

Hint Extern 1 (wfe_tp ?E ?T) =>
  match goal with
  | H: sub_tp E T _ |- _ => apply (proj1 (proj2 (sub_tp_regular H)))
  | H: sub_tp E _ T |- _ => apply (proj2 (proj2 (sub_tp_regular H)))
  end.
