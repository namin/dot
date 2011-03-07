Set Implicit Arguments.
Require Import syntax_binding.
Require Import Metatheory LibTactics_sf support.

Lemma open_lc_decl_ident: forall d t, lc_decl d -> open_decl_cond d t d. Proof. Admitted.
Lemma open_lc_is_noop : forall T x, lc_tp T -> T = T ^tp^ x. Proof. Admitted.

Lemma open_decl_cond_pres_lc_decls  : forall DS l D t T, lc_decls DS -> lbl.binds l D DS -> open_decl_cond D t (decl_tm T) -> lc_tp T.
Proof. Admitted.

(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "../metalib") ***
*** End: ***
*)  