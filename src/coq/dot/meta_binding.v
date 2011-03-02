Set Implicit Arguments.
Require Import syntax_binding.
Require Import Metatheory LibTactics_sf support.

Lemma open_lc_decl_ident: forall d t, lc_decl d -> open_decl_cond d t d. Admitted.
Lemma open_lc_is_noop : forall T x, lc_tp T -> T = T ^tp^ x. Proof. Admitted.
