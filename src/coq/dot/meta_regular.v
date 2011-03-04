Set Implicit Arguments.
Require Import List.
Require Import syntax_binding theory.
Require Import Metatheory LibTactics_sf support.
Require Import meta_pres_subst.
Require Import Coq.Program.Equality.


Lemma regular_expands: forall E T DS q,  E |= T ~< DS @ q -> wf_env E /\ lc_tp T. Admitted.
Lemma regular_subtyping: forall E T T' q,  E |= T ~<: T' @ q -> wf_env E /\ lc_tp T /\ lc_tp T'. Admitted.
Lemma regular_typing: forall E t T q,  E |= t ~: T @ q -> wf_env E /\ lc_tm t /\ lc_tp T. Admitted.

(*Lemma regular_typing: forall E t T q,  E |= t ~: T @ q -> wf_env E /\ lc_tm t /\ lc_tp T. Admitted.
Lemma regular_wf: forall E T,  wf_tp E T -> lc_tp T. Admitted.*)


(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "../metalib") ***
*** End: ***
*)  