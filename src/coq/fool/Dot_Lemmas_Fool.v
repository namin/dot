(** The DOT calculus -- Lemmas *)

Set Implicit Arguments.
Require Import List.
Require Export Dot_Labels.
Require Import Metatheory LibTactics_sf.
Require Export Dot_Syntax Dot_Definitions Dot_Rules_Fool.
Require Import Coq.Program.Equality.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Logic.Decidable.

(* ********************************************************************** *)
(** ** Evaluation *)

Lemma ev_wf_store : forall s s' t t',
  s |~ t ~>~ t' ~| s' -> wf_store s /\ wf_store s'.
Proof.
  introv H. split.
    induction H; try assumption.
      Case "ev_new".
        inversion IHev; subst. assumption.
    induction H; try assumption.
Qed.

Lemma value_xor_method_label : forall l,
  value_label l -> method_label l -> False.
Proof.
  introv Hvalue Hmethod. inversion Hvalue. inversion Hmethod.
  rewrite <- H0 in H. inversion H.
Qed.

Lemma wf_store_lbl_binds_value : forall s l v a Tc ags,
  wf_store s -> binds a (Tc, ags) s -> lbl.binds l v ags -> value_label l -> value v.
Proof.
  introv Hwf Hb Hlb Hvalue. induction Hwf.
  Case "nil". inversion Hb.
  Case "rest".
   rewrite_env ((x, (Tc0, args))::E) in Hb.
   apply binds_cons_1 in Hb. inversions Hb.
   SCase "x = a ".
     inversions H3. inversions H5. 
     remember (H l v Hlb) as H'.
     inversions H'.
       inversions H3. assumption.
       assert False as Contra. apply value_xor_method_label with (l:=l); assumption. inversion Contra.
   SCase "x <> a".
     apply IHHwf.
     assumption.
Qed.

Lemma ev_to_value : forall s s' t v,
  s |~ t ~>~ v ~| s' -> value v.
Proof.
  introv H. induction H; try assumption.
    Case "ev_sel".
      inversion H2; subst.
        apply wf_store_lbl_binds_value with (s:=sf) (l:=lv a0) (a:=a) (Tc:=Tc) (ags:=ags);
        try apply (proj2 (ev_wf_store H));
        assumption.
Qed.

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
        inversions Hbind. inversions H. inversions H1. inversions H1. inversions H0.
        inversions H1. inversions H2. auto. inversions H2. inversions H1. auto. inversions H1. auto.
    SCase "binds <-> bot /\ valid". intros l d. splits.
      SSCase "->". intro Hbind.
        inversions Hbind. inversions H. inversions H1. inversions H1. inversions H0. inversions H.
        inversions H1. inversions H. auto. inversions H. inversions H1. auto. inversions H1. auto.
      SSCase "<-". intro H.
        inversions H. apply decls_binds_inf with (dsl:=nil); auto. inversions H0; inversions H1; auto.
Qed.
Hint Resolve expands_bot_inf_nil.

Lemma expansion_exists : forall E T,
  wfe_tp E T -> exists DS, E |= T ~< DS.
Proof.
  introv Hwfe. inversion Hwfe. subst. exists DT. assumption.
Qed.

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

Ltac add_expands_hyp E T DT HxT :=
  let HxT_ := fresh "HxT_" in
    assert (exists DT, E |= T ~< DT) as HxT_; try solve [apply expansion_exists; eauto 3];
      inversion HxT_ as [DT HxT]; clear HxT_.

Lemma sub_tp_regular : forall E S T,
  E |= S ~<: T ->
  wf_env E /\ wfe_tp E S /\ wfe_tp E T.
Proof.

Hint Extern 1 (wf_env ?E) =>
  match goal with
  | IH: wf_env ?E /\ _ /\ _ |- _ => apply (proj1 IH)
  end.
Hint Extern 1 (wfe_tp ?E ?T) =>
  match goal with
  | IH: _ /\ wfe_tp ?E ?T /\ _ |- _ => apply (proj1 (proj2 IH))
  | IH: _ /\ _ /\ wfe_tp ?E ?T |- _ => apply (proj2 (proj2 IH))
  end.
Hint Extern 2 (wfe_tp ?E (tp_sel ?p ?L)) =>
  match goal with
  | H: ?E |= ?p ~mem~ ?L ~: decl_tp ?S ?U |- _ => let DU := fresh "DU" with HxU := fresh "HxU" in
    add_expands_hyp E U DU HxU; apply wfe_any with (DT:=DU); eauto 3
  end.

Ltac combine_decls E T1 T2 DSM cmb_decls decls_cmb_exists :=
  let DT1 := fresh "DT1" with HxT1 := fresh "HxT1" with DT2 := fresh "DT2" with HxT2 := fresh "HxT2"
    with Hdsm' := fresh "Hdsm'" with Hdsm := fresh "Hdsm" in
      add_expands_hyp E T1 DT1 HxT1; add_expands_hyp E T2 DT2 HxT2;
      assert (exists DSM, cmb_decls DT1 DT2 DSM) as Hdsm'; try solve [apply decls_cmb_exists; eauto 3];
        inversion Hdsm' as [DSM Hdsm].

Ltac wfe_by_combine_decls E T1 T2 cmb_decls decls_cmb_exists :=
  let DSM := fresh "DSM" in combine_decls E T1 T2 DSM cmb_decls decls_cmb_exists;
    apply wfe_any with (DT:=DSM); eauto 3.

Hint Extern 2 (wfe_tp ?E (tp_and ?T1 ?T2)) => wfe_by_combine_decls E T1 T2 and_decls decls_and_exists.
Hint Extern 2 (wfe_tp ?E (tp_or ?T1 ?T2)) => wfe_by_combine_decls E T1 T2 or_decls decls_or_exists.

Hint Constructors wf_tp expands.

Hint Extern 1 (wf_tp ?E ?T) =>
  match goal with
  | IH: wfe_tp ?E ?T |- _ => inversion IH; subst; assumption
  | IH: _ /\ wfe_tp ?E ?T /\ _ |- _ =>
    let Hwfe := fresh "Hwfe" in (assert (wfe_tp E T) as Hwfe);
      try apply (proj1 (proj2 IH)); inversion Hwfe; assumption
  | IH: _ /\ _ /\ wfe_tp ?E ?T |- _ =>
    let Hwfe := fresh "Hwfe" in (assert (wfe_tp E T) as Hwfe);
      try apply (proj2 (proj2 IH)); inversion Hwfe; assumption
  end.

  introv H. induction H; splits; eauto 3.

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
