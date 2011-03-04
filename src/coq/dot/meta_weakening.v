Set Implicit Arguments.
Require Import List.
Require Import syntax_binding theory.
Require Import Metatheory LibTactics_sf support.
Require Import meta_pres_subst.
Require Import Coq.Program.Equality.

(* todo weaken to allow quality to vary *)

(* TODO: bindings in E and E' must be checked for new-well-formedness  -- need to preserve the quality *)
Lemma weakening_expansion: forall E E' T DS q,  dom (fst E)[<=]dom (fst E') -> E |= T ~< DS @ q -> E' |= T ~< DS @ q. Admitted.
Lemma weakening_subtyping: forall E E' S T q,  dom (fst E)[<=]dom (fst E') -> E |= S ~<: T @ q -> E' |= S ~<: T @ q. Admitted.

Lemma weakening_expansion_store: forall E s s' T DS q,  dom s [<=] dom s' -> (E, s) |= T ~< DS @ q -> (E, s') |= T ~< DS @ q. Admitted.
Lemma weakening_subtyping_store: forall E s s' S T q,  dom s [<=] dom s' -> (E, s) |= S ~<: T @ q -> (E, s') |= S ~<: T @ q. Admitted.
Lemma weakening_typing_store: forall E s s' t T q,  dom s [<=] dom s' -> (E, s) |= t ~: T @ q -> exists q, (E, s') |= t ~: T @ q. Admitted.
Lemma weakening_wf_env_store: forall E s a Tc args,  wf_env (E, s) -> wf_env (E, a ~ (Tc, args) ++ s). Admitted.
Lemma weakening_typing: forall E E' t T q,  dom (fst E)[<=]dom (fst E') -> E |= t ~: T @ q -> exists q, E' |= t ~: T @ q. Admitted.


(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "../metalib") ***
*** End: ***
*)  