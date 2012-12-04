(** The DOT calculus -- Theorems *)

Set Implicit Arguments.
Require Import List.
Require Export Dot_Labels.
Require Import Metatheory LibTactics_sf.
Require Export Dot_Syntax Dot_Definitions Dot_Rules Dot_Lemmas.
Require Import Coq.Program.Equality.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Logic.Decidable.

(* ********************************************************************** *)

Theorem tp_wf__expands : forall E T,
  wf_env E -> wf_tp E T -> exists DT, E |= T ~< DT.
Proof.
  intros E T Henv Hwf. induction Hwf.
  Case "rfn".
    specialize (IHHwf Henv). inversion IHHwf as [DT HDT].
    assert (exists DSM, and_decls DT (decls_fin DS) DSM) as HDSM. apply decls_and_exists.
      apply expansion_decls_ok in HDT. assumption. assumption.
    inversion HDSM as [DSM HDSM'].
    exists DSM.
    apply expands_any. apply expands_iter_rfn with (DSP:=DT). inversion HDT; subst; assumption. assumption.
  Case "sel".
    skip. (* TODO *)
  Case "and".
    specialize (IHHwf1 Henv). inversion IHHwf1 as [DT1 HDT1].
    specialize (IHHwf2 Henv). inversion IHHwf2 as [DT2 HDT2].
    assert (exists DSM, and_decls DT1 DT2 DSM) as HDSM. apply decls_and_exists.
      apply expansion_decls_ok in HDT1. assumption.
      apply expansion_decls_ok in HDT2. assumption.
    inversion HDSM as [DSM HDSM'].
    exists DSM.
    apply expands_any. apply expands_iter_and with (DS1:=DT1) (DS2:=DT2).
      inversion HDT1; subst; assumption.
      inversion HDT2; subst; assumption.
      assumption.
  Case "or".
    specialize (IHHwf1 Henv). inversion IHHwf1 as [DT1 HDT1].
    specialize (IHHwf2 Henv). inversion IHHwf2 as [DT2 HDT2].
    assert (exists DSM, or_decls DT1 DT2 DSM) as HDSM. apply decls_or_exists.
      apply expansion_decls_ok in HDT1. assumption.
      apply expansion_decls_ok in HDT2. assumption.
    inversion HDSM as [DSM HDSM'].
    exists DSM.
    apply expands_any. apply expands_iter_or with (DS1:=DT1) (DS2:=DT2).
      inversion HDT1; subst; assumption.
      inversion HDT2; subst; assumption.
      assumption.
  Case "bot".
    exists (decls_inf nil). apply expands_bot_inf_nil. assumption.
  Case "top".
    exists (decls_fin nil). apply expands_any. apply expands_iter_top. assumption.
Qed.

(*
*** Local Variables:
*** coq-load-path: ("metalib" "lib")
*** End:
*)
