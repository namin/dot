Set Implicit Arguments.
Require Import List.
Require Import Metatheory LibTactics_sf Labels.

Ltac injsubst H := (injection H; intros; subst; clear H).

Lemma binds_map_3 : forall A B l v (f: A -> B) args, LabelMapImpl.binds l v ((LabelMapImpl.map f) args) -> exists v', LabelMapImpl.binds l v' args.
Proof. Admitted.
