Set Implicit Arguments.
Require Import List.
Require Import syntax_binding theory.
Require Import Metatheory LibTactics_sf support.
Require Import meta_pres_subst.
Require Import Coq.Program.Equality.

(* todo weaken to allow quality to vary *)

(* TODO: bindings in E and E' must be checked for new-well-formedness  -- do we need to preserve the quality? *)
Lemma weakening_expansion: forall E E' T DS q,  dom (fst E)[<=]dom (fst E') -> E |= T ~< DS @ q -> E' |= T ~< DS @ q. Admitted.

(* TODO: bindings in E and E' must be checked for new-well-formedness  -- do we need to preserve the quality? *)
Lemma weakening_subtyping: forall E E' S T q,  dom (fst E)[<=]dom (fst E') -> E |= S ~<: T @ q -> E' |= S ~<: T @ q. Admitted.

Lemma weakening_typing: forall E E' t T q,  dom (fst E)[<=]dom (fst E') -> E |= t ~: T @ q -> exists q, E' |= t ~: T @ q. Admitted.
