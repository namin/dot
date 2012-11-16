Set Implicit Arguments.
Require Import List.
Require Import syntax_binding theory.
Require Import Metatheory LibTactics_sf support.
Require Import meta_pres_subst.
Require Import Coq.Program.Equality.


(*Lemma expands_regular: forall E T DS q,  E |= T ~< DS @ q -> wf_env E /\ vars_ok_tp T. Admitted. *)

Lemma typing_regular: forall E t T  q,  E |= t ~: T @ q   -> wf_env E /\ lc_tm t      /\ vars_ok_tp E T.  Admitted.
Lemma sub_tp_regular: forall E T T' q,  E |= T ~<: T' @ q -> wf_env E /\ vars_ok_tp E T /\ vars_ok_tp E T'. Admitted.
Lemma red_regular : forall e s e' s', red s e s' e' -> lc_tm e /\ lc_tm e'. Admitted.
(*Proof with try solve [auto | intuition auto].
  intros e e' H.
  induction H; assert(J := value_regular); split...
  Case "red_abs".
    inversion H. pick fresh y. rewrite (subst_ee_intro y)...
  Case "red_tabs".
    inversion H. pick fresh Y. rewrite (subst_te_intro Y)...
Qed.*)


(*
Lemma regular_sub_tp_vars_ok_1 : forall E S T q, 
 E |= S ~<: T @ q -> vars_ok_tp E S.
Proof. Admitted. (* TODO *)
*)

Lemma lc_tp_from_vars_ok_tp : forall E T,
  vars_ok_tp E T -> lc_tp T.
Proof. Admitted.
(* Hint Constructors lc_tp.
  intros E T H; induction H; eauto.
Qed.*)
(*Hint Resolve lc_tp_from_vars_ok_tp.*)


(** The lemma [uniq_from_wf_env] was already added above as a hint
    since it helps blur the distinction between [wf_env] and [uniq] in
    proofs.

    As currently stated, the regularity lemmas are ill-suited to be
    used with [auto] and [eauto] since they end in conjunctions.  Even
    if we were, for example, to split [sub_regularity] into three
    separate lemmas, the resulting lemmas would be usable only by
    [eauto] and there is no guarantee that [eauto] would be able to
    find proofs effectively.  Thus, the hints below apply the
    regularity lemmas and [type_from_wf_typ] to discharge goals about
    local closure and well-formedness, but in such a way as to
    minimize proof search.

    The first hint introduces an [wf_env] fact into the context.  It
    works well when combined with the lemmas relating [wf_env] and
    [wf_typ].  We choose to use those lemmas explicitly via [(auto
    using ...)] tactics rather than add them as hints.  When used this
    way, the explicitness makes the proof more informative rather than
    more cluttered (with useless details).

    The other three hints try outright to solve their respective
    goals. *)

(* NOTE THIS IS FRAGILE WRT IMPLICIT ARGUMENTS (how can I debug why a tactic fails, e.g., because the arguments are wrong since I'm explicitly supply implicit arguments...)*)
(* is it better style to prefix with @ and supply all args as underscores!?? *)
Hint Extern 1 (vars_ok_tp ?E ?T) =>
  match goal with
  | H: typing E _ _ T |- _ => apply (proj2 (proj2 (typing_regular H))); auto
  | H: sub_tp E _ T _ |- _ => apply (proj1 (proj2 (sub_tp_regular H))); auto
  | H: sub_tp E _ _ T |- _ => apply (proj2 (proj2 (sub_tp_regular H))); auto
  end.

Hint Extern 1 (lc_tp ?T) =>
  match goal with
  | H: typing ?E _ _ T |- _ => apply (@lc_tp_from_vars_ok_tp E T); auto
  | H: sub_tp ?E _ T _ |- _ => apply (@lc_tp_from_vars_ok_tp E T); auto
  | H: sub_tp ?E _ _ T |- _ => apply (@lc_tp_from_vars_ok_tp E T); auto
  end.

Hint Extern 1 (lc_tp ?T) =>
  match goal with
  | H: typing ?E _ _ T |- _ => apply (@lc_tp_from_vars_ok_tp E T)
  | H: sub_tp ?E _ T _ |- _ => apply (@lc_tp_from_vars_ok_tp E T)
  | H: sub_tp ?E _ _ T |- _ => apply (@lc_tp_from_vars_ok_tp E T)
  end.


Hint Extern 1 (lc_tm ?e) =>
  match goal with
  | H: typing _ _ ?e _ |- _ => apply (proj1 (proj2 (typing_regular H))); auto
  | H: red _ ?e _ _ |- _ => apply (proj1 (red_regular H)); auto
  | H: red _ _ _ ?e |- _ => apply (proj2 (red_regular H)); auto
  end.


(*Lemma regular_typing: forall E t T q,  E |= t ~: T @ q -> wf_env E /\ lc_tm t /\ lc_tp T. Admitted.
Lemma regular_wf: forall E T,  wf_tp E T -> lc_tp T. Admitted.*)


(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "../metalib") ***
*** End: ***
*)  