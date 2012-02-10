Set Implicit Arguments.
Require Import List.
Require Import syntax_binding theory theory_alg.
Require Import Metatheory LibTactics_sf support meta_regular meta_binding meta_weakening meta_narrowing meta_alg_sub_trans.
Require Import Coq.Program.Equality.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Logic.Decidable.

Definition ex1 := lam tp_top (bvar 0).

Hint Constructors typing_alg path_eq_alg wf_env_alg sub_tp_alg sub_decl_alg wf_tp_alg wf_decl_alg.
Hint Constructors lc_tp lc_decl lc_tm lc_decls lc_args.
Hint Constructors vars_ok_tp vars_ok_decl  vars_ok_tm vars_ok_decls vars_ok_args.
Hint Constructors path_safe.
Hint Unfold open open_rec_tm.

Lemma test1: exists T, (nil,nil) |= ex1 ~:! T.
  intros. unfold ex1. exists (tp_fun tp_top tp_top).
  pick fresh x and apply typing_alg_lam.
  unfold open. unfold open_rec_tm. simpl.
  eapply typing_alg_var.
  eauto.
  eauto.
  eauto.
  eauto.
Qed.

Section Bad.
Parameter x : var.
Parameter L : label.

Definition E := ctx_bind_subsumed (nil,nil) x (tp_rfn tp_top [(L, decl_tp tp_top tp_bot)]).

Lemma bad: E |= tp_top ~<! tp_bot.
Proof.
  apply sub_tp_alg_trans with (TMid:=tp_sel x L).
  apply sub_tp_alg_tpsel_r with (T':=(tp_rfn tp_top [(L, decl_tp tp_top tp_bot)])) (DS:=[(L, decl_tp tp_top tp_bot)]) (S:=tp_top) (U:=tp_bot).
  eauto.
  eapply typing_alg_var.
  apply wf_env_alg_cons. eauto. simpl. apply vars_ok_tp_rfn with (L:=empty). eauto.
    intros. simpl. eauto. eauto.
  apply lc_tp_rfn with (L:=empty). eauto.
    intros. simpl. eauto.
  eauto.
  eauto.
  eapply path_safe_fvar. eauto.
  eauto.
  apply sub_tp_alg_tpsel_l with (T':=(tp_rfn tp_top [(L, decl_tp tp_top tp_bot)])) (DS:=[(L, decl_tp tp_top tp_bot)]) (S:=tp_top) (U:=tp_bot).
  eauto.
  eapply typing_alg_var.
  apply wf_env_alg_cons. eauto. simpl. apply vars_ok_tp_rfn with (L:=empty). eauto.
    intros. simpl. eauto. eauto.
  apply lc_tp_rfn with (L:=empty). eauto.
    intros. simpl. eauto.
  eauto.
  eauto.
  eauto.
  eauto.
Qed.
End Bad.
