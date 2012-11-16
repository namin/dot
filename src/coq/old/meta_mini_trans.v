Set Implicit Arguments.
Require Import List.
Require Import syntax_binding theory_mini.
Require Import Metatheory LibTactics_sf support.

Definition ordered_tp E T T' := E |= T ~<% T' \/ E |= T' ~<% T.
Definition ordered_decl E D D' := sub_decl_mini E D D' \/ sub_decl_mini E D' D.
Hint Unfold ordered_tp.

Definition transitivity_on TMid := forall E T T',  E |= T ~<% TMid -> E |= TMid ~<% T' -> E |= T ~<% T'.
Hint Unfold transitivity_on.


(* TODO: requires well-kindedness of environment *)
Lemma ordered_pres : 
  (forall (E : env) (p : tm) (T : tp) (H : E |= p ~:% T)  T', path p -> E |= p ~:% T' -> ordered_tp E T T') /\
  (forall (E : env) (H : wf_env_mini E), True) /\
  (forall (E : env) (T1 T2 : tp) (H : E |= T1 ~<% T2) T1' T2', E |= T1' ~<% T2' -> ordered_tp E T1 T1' -> ordered_tp E T2 T2') /\
  (forall (E : env) (D1 D2 : decl) (H : sub_decl_mini E D1 D2) D1' D2', sub_decl_mini E D1' D2' -> ordered_decl E D1 D1' -> ordered_decl E D2 D2') /\
  (forall (E : env) (T : tp) (H : wf_tp_mini E T), True).

Proof.
Check typing_mini_mutind.


(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "../metalib") ***
*** End: ***
*)  