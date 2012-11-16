Set Implicit Arguments.
Require Import List.
Require Import Metatheory LibTactics_sf Labels.

Ltac injsubst H := (injection H; intros; subst; clear H).

Module lbl := LabelMapImpl.

Tactic Notation "decls" "induction" ident(E) :=
  try (intros until E);
  let T := type of E in
  let T := eval compute in T in
  match T with
    | list (label * ?A) => induction E using (lbl.alist_ind A)
  end.

Lemma binds_map_3 : forall A B l v (f: A -> B) args, lbl.binds l v ((lbl.map f) args) -> exists v', lbl.binds l v' args.
Proof. Admitted.
