Set Implicit Arguments.
Require Import List.
Require Import syntax_binding theory_mini.
Require Import Metatheory LibTactics_sf support.


Definition exposed E p L S U := exists T DS,  path p /\ E |= p ~:% T /\ E |= T ~<% (tp_rfn tp_top DS) /\ lbl.binds L (decl_tp S U) DS.
Hint Unfold exposed.

(* strategy for sub_tp_alg_trans_tpsel

(`expose p.L S U` is short for   p : T0 {... L : S'..U' ...} where S = S' ^^ p, U = U' ^^ p)

[case for sub_tp_alg_trans: type selection on the inside]

                 expose p.L S U       expose p.L S' U'
[sub_tp_tpsel_r]----------------     ----------------[sub_tp_tpsel_l]
                     S <: p.L          p.L <: U'

NTS: S <: U'

required lemma's, which hopefully do not require transitivity -- BZZZZ they do need it

splice: expose p.L S U -> expose p.L S' U' -> expose p.L S U'

  this should be provable by inverting the typing/subtyping judgements that derive exposure, 
  cutting each of them in half and splicing them back together to get the required mongrel
  (if they derive new bounds for L, there must be a sub_decl judgement involved, which is simply 
  subtyping of the lower and upper bound according to the variance position, thus we can piece together
  a new sub_decl judgement from the appropriate halves of each one) 
  
  --> the problem is you need to induct on these derivations and fuse them together, which requires transitivity

invert_expose: expose p.L S U' -> S <: U' (under suitable side conditions of well-formedness of the context)


[case for sub_tp_alg_trans: type selection on the outside -- actually two symmetric cases]

                expose p.L S U
[sub_tp_tpsel_l]----------------   ----------[??]
                    p.L <: U         U <: T

invert the sub_tp_alg_rfn_r in expose p.L S U, reconstruct new one by incorporating U <: T
done

*)

(*
mutually induct
need transitivity on types of p (T, T') for path selection case during induction
*)
Lemma alg_typing_sub_tp_function_modulo_sub_tp : 
  forall E p T T', path p -> E |= p ~:% T -> E |= p ~:% T' -> E |= T ~<% T' \/ E |= T' ~<% T.
  forall E p T DS L D DS' D', path p -> E |= T ~<% (tp_rfn tp_top DS) -> lbl.binds L D DS -> E |= T ~<% (tp_rfn tp_top DS') -> lbl.binds L D' DS'
  -> sub_decl_alg E (D ^d^ p) (D' ^d^ p) \/ sub_decl_alg E (D' ^d^ p) (D ^d^ p).
Proof.


Lemma splice_exposed : forall E p T T', path p -> E |= p ~:% T -> E |= p ~:% T' -> True.
Proof.
  introv Hp Htp Htp'.  skip. skip. skip. skip. skip. skip. skip. skip. skip. skip. skip. skip.  skip. 
    unfold exposed in Hxpo. inversion Hxpo as [T [DS [Hpath [Htp [Hsub Hbind]]]]].
    unfold exposed in Hxpo'. inversion Hxpo' as [T' [DS' [_ [Htp' [Hsub' Hbind']]]]]. clear Hxpo Hxpo'.
    induction p; inverts Hpath; inverts Htp; inverts Htp'. ; dependent induction Hsub; dependent induction Hsub'.
 induction Hpath; inverts Htp; inverts Htp'; eauto. skip. skip. skip. skip. skip. skip. skip. skip. skip.
   
Lemma sub_tp_alg_trans_tpsel : forall E q1 q2 p T DS l S U T' DS' S' U' Ta Tb,
  path_safe E p ->

  E |= p ~: T @ q1 ->
  E |= T ~<% tp_rfn tp_top DS ->
  lbl.binds l (decl_tp S U) DS ->

  E |= p ~: T' @ q2 -> 
  E |= T' ~<% tp_rfn tp_top DS' ->
  lbl.binds l (decl_tp S' U') DS' ->

  E |= Ta ~<% S ^tp^ p ->
  E |= U' ^tp^ p ~<% Tb ->

  E |= Ta ~<% Tb.
Proof. Admitted. (* TODO *)


Definition transitivity_on TMid := forall E T T',  E |= T ~<% TMid -> E |= TMid ~<% T' -> E |= T ~<% T'.
Hint Unfold transitivity_on.



(* inspired by sub_transitivity from http://www.chargueraud.org/arthur/research/2007/binders/src/Fsub_Soundness.html

  Coq provides "dependent induction" to perform "Induction/inversion principle"; 4.2.1. of
   http://www.msr-inria.inria.fr/~gares/jar09.pdf explains the latter is needed to perform a proof like this
*)
Lemma sub_tp_alg_trans : forall TMid, transitivity_on TMid.
Proof.
 introv HSubL HSubR. gen E T T'. gen_eq TMid as TMid' eq. gen TMid' eq. 
 induction TMid; intros; gen T';
   induction HSubL; try discriminate; inversions eq; intros; 
     generalize_eqs_vars HSubR; induction HSubR; simplify_dep_elim; subst; auto; try solve [ 
       eapply sub_tp_alg_rfn_r; eauto 2; eapply narrow_sub_decls; eauto 2 |
       eapply sub_tp_alg_and_r; eauto 2 | 
       eapply sub_tp_alg_and_l1; eapply IHHSubL; eauto 2 |
       eapply sub_tp_alg_and_l2; eapply IHHSubL; eauto 2 |
       eapply sub_tp_alg_rfn_l; eapply IHHSubL; eauto 2 |
       eapply sub_tp_alg_tpsel_l; eauto 3 using sub_tp_alg_rfn_r |
       eapply sub_tp_alg_or_l; eauto 3 using IHHSubL1, sub_tp_alg_tpsel_l, IHHSubL2 |
       eapply sub_tp_alg_rfn_r; eauto 3 using IHHSubR1, narrow_sub_decls, sub_tp_alg_rfn_r, IHHSubR2 |
       eapply sub_tp_alg_fun; eauto 2 using IHTMid1, IHTMid2 |
       eauto 3]. (* less than 2 minutes*)

(* TODO: the core case... do we need to introduce some kind of sub_tp_alg rule? as in fsub? *)
rename t into p. rename T into Ta. rename T0 into Tb'. rename T' into Twoele. rename T'0 into T'. rename Twoele into T.
rename DS0 into DS'. rename S0 into S'. rename U0 into U'. rename q0 into q'. rename q1 into q.

clear IHHSubR1 IHHSubR2 IHHSubL1 IHHSubL2.
(*
  H1 : path_safe E p
  H4 : path p

  H0 : E |= p ~: T @ q
  HSubL2 : E |= T ~<% tp_rfn tp_top DS
  H : lbl.binds l (decl_tp S U) DS

  H3 : E |= p ~: T' @ q'
  HSubR2 : E |= T' ~<% tp_rfn tp_top DS'
  H2 : lbl.binds l (decl_tp S' U') DS'

  HSubL1 : E |= Ta ~<% S ^tp^ p
  HSubR1 : E |= U' ^tp^ p ~<% Tb'
  ============================
   E |= Ta ~<% Tb
*)

 eapply sub_tp_alg_trans_tpsel with (T' := T'); eauto.
Qed.
