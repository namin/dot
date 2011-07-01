Set Implicit Arguments.
Require Import List.
Require Import syntax_binding theory theory_alg.
Require Import Metatheory LibTactics_sf support meta_regular meta_binding meta_weakening meta_narrowing.
Require Import Coq.Program.Equality.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Logic.Decidable.


(* the motivation for the alg version of subtyping: inversion *)
Lemma invert_fun_alg : forall E Sa Sr Ta Tr,
  E |= tp_fun Sa Sr ~<! tp_fun Ta Tr ->
  E |= Ta ~<! Sa  /\  E |= Sr ~<! Tr.
Proof.
intros.
inverts H; splits; auto using sub_tp_alg_refl.
Qed.

(* NEEDED BY PRESERVATION (needs soundness and completeness of the algorithmic system + invert_fun_alg)
Lemma invert_subtyping_fun : 
   (forall E q T DS, E |= T ~< DS @ q -> forall T1 T2, is_fun T T1 T2 -> DS = nil) /\
   (forall E q S T, E |= S ~<: T @ q -> forall T1 T2, is_fun S T1 T2 ->
      (exists T1', exists T2', is_fun T T1' T2' /\ (exists q, E |= T1' ~<: T1 @ q /\ exists q, E |= T2 ~<: T2' @ q))).

*)

Hint Constructors sub_tp_alg sub_decl_alg.





Definition exposed E p L S U := exists T DS,  path p /\ E |= p ~:! T /\ E |= T ~<! (tp_rfn tp_top DS) /\ lbl.binds L (decl_tp S U) DS.
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
  forall E p T T', path p -> E |= p ~:! T -> E |= p ~:! T' -> E |= T ~<! T' \/ E |= T' ~<! T.
  forall E p T DS L D DS' D', path p -> E |= T ~<! (tp_rfn tp_top DS) -> lbl.binds L D DS -> E |= T ~<! (tp_rfn tp_top DS') -> lbl.binds L D' DS'
  -> sub_decl_alg E (D ^d^ p) (D' ^d^ p) \/ sub_decl_alg E (D' ^d^ p) (D ^d^ p).
Proof.


Lemma splice_exposed : forall E p T T', path p -> E |= p ~:! T -> E |= p ~:! T' -> True.
Proof.
  introv Hp Htp Htp'.  skip. skip. skip. skip. skip. skip. skip. skip. skip. skip. skip. skip.  skip. 
    unfold exposed in Hxpo. inversion Hxpo as [T [DS [Hpath [Htp [Hsub Hbind]]]]].
    unfold exposed in Hxpo'. inversion Hxpo' as [T' [DS' [_ [Htp' [Hsub' Hbind']]]]]. clear Hxpo Hxpo'.
    induction p; inverts Hpath; inverts Htp; inverts Htp'. ; dependent induction Hsub; dependent induction Hsub'.
 induction Hpath; inverts Htp; inverts Htp'; eauto. skip. skip. skip. skip. skip. skip. skip. skip. skip.
   
Lemma sub_tp_alg_trans_tpsel : forall E q1 q2 p T DS l S U T' DS' S' U' Ta Tb,
  path_safe E p ->

  E |= p ~: T @ q1 ->
  E |= T ~<! tp_rfn tp_top DS ->
  lbl.binds l (decl_tp S U) DS ->

  E |= p ~: T' @ q2 -> 
  E |= T' ~<! tp_rfn tp_top DS' ->
  lbl.binds l (decl_tp S' U') DS' ->

  E |= Ta ~<! S ^tp^ p ->
  E |= U' ^tp^ p ~<! Tb ->

  E |= Ta ~<! Tb.
Proof. Admitted. (* TODO *)


Definition transitivity_on TMid := forall E T T',  E |= T ~<! TMid -> E |= TMid ~<! T' -> E |= T ~<! T'.
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
  HSubL2 : E |= T ~<! tp_rfn tp_top DS
  H : lbl.binds l (decl_tp S U) DS

  H3 : E |= p ~: T' @ q'
  HSubR2 : E |= T' ~<! tp_rfn tp_top DS'
  H2 : lbl.binds l (decl_tp S' U') DS'

  HSubL1 : E |= Ta ~<! S ^tp^ p
  HSubR1 : E |= U' ^tp^ p ~<! Tb'
  ============================
   E |= Ta ~<! Tb
*)

 eapply sub_tp_alg_trans_tpsel with (T' := T'); eauto.
Qed.

(*
sub_tp_alg_or_l, sub_tp_alg_trans_tpsel, sub_tp_alg_trans_rfn_rfn, 
       try solve [ apply IHHSubR; eauto | 
                   apply sub_tp_alg_or_l; eauto | 
                   eauto using rework_sub_decls |
                   eapply sub_tp_alg_trans_tpsel with (T' := T'); eauto |
                   eapply sub_tp_alg_trans_rfn_rfn; eauto |
                   ]. (* 7 min *)
*)




Section AlgCompleteness.

    Let P2_ (E : env) (q : quality) (S T : tp) (H: E |= S ~<: T @ q) := E |= S ~<! T.
    Let P1_ (E : env) (q : quality) (T : tp) (DS : decls) (H: E |= T ~< DS @ q) := E |= T ~<! tp_rfn tp_top DS.

    Let P0_ (E_s: env) (q: quality) (t: tm) (T: tp) (H: E_s |=  t ~: T  @ q) := True.
    Let P3_ (e : env) (q : quality) (d d0 : decl) (H: sub_decl e q d d0) := True.
    Let P4_ (e : env) (t t0 : tm) (H: path_eq e t t0) := True.
    Let P5_ (e : env) (H: wf_env e) := True.
    Let P6_ (e : env) (t : tp) (H: wf_tp e t) := True.
    Let P7_ (e : env) (d : decl) (H: wf_decl e d) := True.

  (* only hard case is sub_tp_trans, which is proven above *)
  Lemma alg_is_complete : (forall E q S T, E |= S ~<: T @ q -> E |= S ~<! T) /\ (forall E q T DS, E |= T ~< DS @ q -> E |= T ~<! tp_rfn tp_top DS).
  Proof.
    cut ((forall E q t T (H: E |= t ~: T @ q), (@P0_ E q t T H)) /\ 
    (forall E q T DS (H: E |= T ~< DS @ q), (@P1_ E q T DS H)) /\ 
    (forall E q T T' (H: E |= T ~<: T' @ q), (@P2_  E q T T' H))  /\ 
    (forall (e : env) (q : quality) (d d0 : decl) (H : sub_decl e q d d0), (@P3_ e q d d0 H)) /\  
    (forall (e : env) (t t0 : tm) (H : path_eq e t t0), (@P4_ e t t0 H)) /\  
    (forall (e : env) (H : wf_env e), (@P5_ e H)) /\
    (forall (e : env) (t : tp) (H : wf_tp e t), (@P6_ e t H)) /\  
    (forall (e : env) (d : decl) (H : wf_decl e d), (@P7_ e d H))); [tauto | 
      apply (typing_mutind P0_ P1_ P2_ P3_ P4_ P5_ P6_ P7_); unfold P0_, P1_, P2_, P3_, P4_, P5_, P6_, P7_ in *; clear P0_ P1_ P2_ P3_ P4_ P5_ P6_ P7_]; intros; eauto 3. 

    apply sub_tp_alg_trans with (TMid := U); eauto.
    eapply sub_tp_alg_rfn_r; eauto. 
    skip. (* TODO: sub_decls_alg_refl *) skip.
    eapply sub_tp_alg_rfn_r with (DS1 := DS1); eauto 2. 
    skip. (* TODO: IH for sub_decls (change from True above to something useful) *)
    apply and_decls_nil_1.
    apply sub_tp_alg_trans with (TMid := TMid); eauto.
  Qed.

End AlgCompleteness.




Section Soundness.
  (* TODO: deal with regularity  *)
  Lemma wf_ax : forall E, wf_env E. Proof. Admitted. (* TODO: used in cases for expands_top and expands_bot *)
  Lemma lc_ax : forall T, lc_tp T. Proof. Admitted. (* TODO: used in cases for sub_tp_rfn_elim *) 
  Hint Resolve wf_ax lc_ax.

  Hint Constructors sub_decl sub_qual path_eq wf_env wf_tp wf_decl.
  Hint Resolve sub_tp_rfn sub_tp_rfn_elim sub_tp_tpsel_lower sub_tp_tpsel_upper sub_tp_top sub_tp_bot sub_tp_fun sub_tp_and_r sub_tp_or_l sub_tp_and_l1 sub_tp_and_l2 sub_tp_or_r1 sub_tp_or_r2 theory.expands_rfn theory.expands_and theory.expands_or theory.expands_top theory.expands_bot sub_tp_refl. (*but not transitivity*)

  Lemma and_decls_nil: and_decls nil nil nil.            Proof. Admitted. (* TODO *)
  Lemma and_decls_nil_1: forall DS, and_decls nil DS DS. Proof. Admitted. (* TODO *)
  Lemma and_decls_nil_2: forall DS, and_decls DS nil DS. Proof. Admitted. (* TODO *)
  Lemma or_decls_nil: or_decls nil nil nil.              Proof. Admitted. (* TODO *)
  Lemma or_decls_nil_1: forall DS, or_decls nil DS nil.  Proof. Admitted. (* TODO *)
  Lemma or_decls_nil_2: forall DS, or_decls DS nil nil.  Proof. Admitted. (* TODO *)

  (* TODO: proof will need decls_ok DS from well formedness of the type that expanded to DS for uniqueness of labels, and wf_env for sub_tp_refl *)
  Lemma sub_decls_refl : forall L E T DS,
     forall z : atom,
     z `notin` L ->
     forall_decls (ctx_bind E z T) (DS ^ds^ z) 
       (DS ^ds^ z)
       (fun (E0 : env) (d1 d2 : decl) => sub_decl E0 subsumed d1 d2).
  Proof. Admitted. (* TODO *) (*
    unfold forall_decls. intros. set (DS' := DS ^ds^ z) in *. 
    gen d1 d2.
    decls induction DS'; intros. 
      inversion H1.

      assert (lbl.uniq DS') as HUnique by admit. (* wf_decls *)
      forwards: (lbl.binds_cons_uniq_1 _ _ _ _ _ _ HUnique H0); eauto. forwards: (lbl.binds_cons_uniq_1 _ _ _ _ _ _ HUnique H1); eauto.
      destruct H2 as [[HEq HEq'] | IH']; destruct H3 as [[HEq1 HEq1'] | IH1']; subst; eauto.
      skip. (*refl*)
      eapply IHDS'; eauto.
*)

Lemma sub_decls_sound : forall L E DS1 DS2 T,
  (forall z : atom, z `notin` L -> forall (l : label) (d1 d2 : decl),
   lbl.binds l d2 (DS2 ^ds^ z) -> lbl.binds l d1 (DS1 ^ds^ z) ->
     exists q, sub_decl (ctx_bind E z T) q d1 d2) ->
  (forall z : atom, z `notin` L ->
   forall_decls (ctx_bind E z T) (DS1 ^ds^ z) (DS2 ^ds^ z)
     (fun (E0 : env) (d1 d2 : decl) => sub_decl E0 subsumed d1 d2)).
Proof.
  unfold forall_decls. intros. destruct (H z H0 l d1 d2 H1 H2) as [q Hsub].
  inverts Hsub; [ apply sub_decl_tp with (q1 := q1) (q2 := q2) (q := subsumed); eauto |
    apply sub_decl_tm with (q1 := q1) (q := subsumed); eauto].
Qed.

  Hint Resolve and_decls_nil and_decls_nil_1 and_decls_nil_2 or_decls_nil or_decls_nil_1 or_decls_nil_2 sub_decls_refl sub_decls_sound.

  (* specialize hypotheses with satisfiable embedded equalities, drop the unsatisfiable ones *)
  Ltac sphyps :=
    repeat match goal with H: ?T |- _ => 
      match T with
      | forall x, ?a = _ -> _  =>  (* TODO: why does generalized `context [ ?a = _ ] ` version not work? *)
        match type of a with
          | ?x => try (let h := fresh in lets h: H (@eq_refl x); generalizes h); clear H
        end
      | _ => generalizes H
      end
    end.
  Ltac simplhyps :=  jauto_set_hyps; intros; sphyps; intros; jauto_set_hyps; intros.

  (* automate most uses of trans (all except for the trans T one, probably), since we know what its argument should be: for a subgoal that needs to show `exists q, E |= T ~<: tp_sel p L @ q`, the argument is `S` if there is a hypothesis `E |= T ~<! ?S` 
   also, these hints avoid uninstantiated existentials that would arise if we were to let eauto have at it with expands_sub and sub_tp_trans *)
  Hint Extern 2 (exists q, ?E |= ?T ~<: _ @ q) =>
    match goal with
    | H: E |= T ~<! ?S |- _ => eexists; eapply sub_tp_trans with (TMid := S); eauto 3
    end.
  Hint Extern 2 (exists q, ?E |= _ ~<: ?T @ q) =>
    match goal with
    | H: E |= ?S ~<! T |- _ => eexists; eapply sub_tp_trans with (TMid := S); eauto 3
    end.
  Hint Extern 2 (exists q, ?E |= _ ~< ?DS @ q) =>
    match goal with
    | H: E |= ?S ~< DS @ _ |- _ => eexists; eapply expands_sub with (U := S); eauto 3
    end.

  Ltac sub_tp_rfn_top DS := 
    eapply sub_tp_rfn with (DS1 := DS) (DS2 := DS) (q := subsumed); [
      eauto 3 | eauto 3 | pick fresh z and apply sub_decls_refl | fsetdec | intros; discriminate].

(* TODO: switch to full mutual induction that includes typing: also need to prove it sound *)
  Let P (E : env) (T1 T2 : tp) (H : E |= T1 ~<! T2) := (exists q, E |= T1 ~<: T2 @ q) /\ (forall DS, T2 = tp_rfn tp_top DS -> exists q, E |= T1 ~< DS @ q).
  Let P0 (E : env) (D1 D2 : decl) (H : sub_decl_alg E D1 D2) := exists q, sub_decl E q D1 D2.
  Lemma alg_is_sound : (forall (E : env) (T1 T2 : tp) (H : E |= T1 ~<! T2), @P E T1 T2 H) /\
              (forall (E : env) (D1 D2 : decl) (H : sub_decl_alg E D1 D2), @P0 E D1 D2 H). 
  Proof. Admitted. (*unfold P, P0. clear P P0.
    apply sub_tp_alg_mutind; first [ (split; 
         [ (* subtyping *) simplhyps; try solve [ exists precise; eauto (* to instantiate sub_tp_refl's existential quality *) | eauto 3 | idtac ]
         | (* expansion *) introv HEq; try injsubst HEq; subst; 
             try destructs IHsub_tp_alg1; try destructs IHsub_tp_alg2; try destructs IHsub_tp_alg; 
             simplhyps; try solve [ discriminate | eauto 2 | eexists; eapply expands_sub; eauto 2 | eexists; intros; eauto 3]]) 
         | (* sub_decl *) intros; exists subsumed; simplhyps; eauto 
      ].

      [ eexists; eapply sub_tp_trans with (TMid := tp_sel p L); eauto using sub_tp_trans
      | eexists; eapply expands_sub with (U := tp_sel p L); eauto  using sub_tp_trans
      | eexists; eapply sub_tp_rfn with (L := L) (DS1 := DS1) (DS2 := DS2) (q := subsumed); eauto 3 using expands_sub; intros; discriminate
      | eexists; eapply expands_sub with (U := tp_rfn tp_top DS0); eauto; eapply sub_tp_rfn with (q1 := x & x1); eauto using expands_sub; intros; discriminate
      | eexists; eapply sub_tp_trans with (TMid := tp_and T1 T2); [eauto 2 | sub_tp_rfn_top DSM]
      | eexists; eapply sub_tp_trans with (TMid := tp_or T1 T2); [eauto 2 | sub_tp_rfn_top DSM]
      | eexists; sub_tp_rfn_top (nil : decls); eauto using expands_sub
      | eexists; eapply expands_sub with (U := tp_rfn tp_top DS); eauto].
  Qed. (* 5s *) *)
End Soundness.
(* Show Existentials is your friend when combatting uninstantiated existentials before Coq will let you Qed *)




Section Narrowing.
  (* specialize hypotheses with satisfiable embedded equalities, drop the unsatisfiable ones *)
  Ltac sphyps :=
    repeat match goal with H: ?T |- _ => 
      match T with
      | context [?a = _]  => 
        match type of a with
          | ?x => try (let h := fresh in lets h: H (@eq_refl x); generalizes h); clear H
        end
      | _ => generalizes H
      end
    end.
  Ltac simplhyps :=  jauto_set_hyps; intros; sphyps; intros; jauto_set_hyps; intros.

  Hint Unfold splice_env.

  Let P (E: ctx) (s: store) (Sz Tz: tp) (Ez : env) (S T : tp) (H : Ez |= S ~<! T) := forall F z, 
    Ez = splice_env E z F s Tz -> (splice_env E z F s Sz) |= S ~<! T.

  Let P0 (E: ctx) (s: store) (Sz Tz: tp) (Ez : env) (D1 D2 : decl) (H : sub_decl_alg Ez D1 D2) := forall F z,
    Ez = splice_env E z F s Tz -> sub_decl_alg (splice_env E z F s Sz) D1 D2.

Lemma sub_narrowing_aux : forall s E Sz Tz,
(*  transitivity_on Tz -> *)
  (E, s) |= Sz ~<! Tz ->
    (forall (Ez : env) (T1 T2 : tp) (H : Ez |= T1 ~<! T2), @P E s Sz Tz Ez T1 T2 H) /\
    (forall (Ez : env) (D1 D2 : decl) (H : sub_decl_alg Ez D1 D2), @P0 E s Sz Tz Ez D1 D2 H).
Proof. 
  unfold P, P0. clear P P0. introv (*HTrans*) HSubZ. 
  destruct (proj1 ((proj1 alg_is_sound) _ _ _ HSubZ)) as [qsz Hsz].

  apply sub_tp_alg_mutind; intros; subst; simplhyps; eauto 4.

(*Hint Extern 1 (splice_env ?E ?z ?F ?s ?Sz |= ?p ~: ?T @ ?q) =>
  match goal with
  | H:  splice_env E z F s ?Tz |= p ~: T @ ?q' |- _ => (idtac; match goal with
     | Hsz: (E, s) |= Sz ~<: Tz @ ?qs |- _ => 
         let qn := fresh in let Hn := fresh in
         lets [qn Hn] : ((proj1 (sub_narrowing_typing Hsz)) _ _ _ _ H F z); [auto | eauto 2 | eapply Hn]
    end)
  end.*)
  
  Hint Resolve narrowing_vars_ok_tp narrowing_path_safe.
  forwards [qn Hn] : (proj1 (sub_narrowing_typing Hsz)); eauto 2.
  eapply sub_tp_alg_tpsel_r; unfold splice_env in *; eauto. 

  eapply sub_tp_alg_rfn_r; eauto.   
    intros zd Frd.  specialize (H1 zd Frd). 
    unfold forall_decls, ctx_bind, splice_env in *. simpl in *. simpl_env in *.
  intros. forwards : H1; eauto. simpl; f_equal. instantiate (1 := z). instantiate (1 :=  (zd, (T, (precise, true))) :: F). trivial. simpl_env in *. trivial.

  forwards [qn Hn] : (proj1 (sub_narrowing_typing Hsz)); eauto 2.
Qed.
  End Narrowing.
Lemma narrow_sub_decls: forall L E S T DS1 DS2,  
(*  transitivity_on T ->*)
  E |=  S ~<! T ->
  (forall z : atom, z `notin` L ->
     forall_decls (ctx_bind E z T) (DS1 ^ds^ z) (DS2 ^ds^ z) sub_decl_alg) -> 
  (forall z : atom, z `notin` L ->
     forall_decls (ctx_bind E z S) (DS1 ^ds^ z) (DS2 ^ds^ z) sub_decl_alg).
Proof. 
  unfold forall_decls. intros. forwards : H0; eauto. unfold ctx_bind in *. destruct E. simpl in *. 
  forwards : (proj2 (sub_narrowing_aux H)); eauto. unfold splice_env; simpl; f_equal. instantiate (1 := z). instantiate (1 := nil). auto. eapply H5.
Qed.

Hint Resolve narrow_sub_decls.




(* more convenient interface to above *)
Lemma invert_expands_fun: forall E S T DS q,  E |= tp_fun S T ~< DS @ q -> DS = nil.
Proof. Admitted. (* TODO *)


Lemma invert_expands_concrete : forall E s Tc DS q, (E, s) |= Tc ~< DS @ q -> concrete Tc -> 
    exists DS', (E, s) |= Tc ~< DS' @ precise /\ exists q, sub_decls (E, s) q DS' DS.
Proof. Admitted. (* TODO *)


(* XXXX need to strenghten definition of E |= ok *)
Lemma sub_tp_trans_safe : forall E s S TMid T q1 q2, 
  E |== s -> (E, s) |= ok -> (E, s) |= S ~<: TMid @ q1 -> (E, s) |= TMid ~<: T @ q2 -> exists q3, (E, s) |= S ~<: T @ q3.
Proof. Admitted. (* TODO *)  
(*
  intros.  set TMid as TMid'. dependent induction TMid; try solve [exists (q1 & q2); apply sub_tp_trans with (TMid := TMid'); auto; unfold not; intros ? ? HH; inversion HH | idtac]; clear TMid'.   
 
  destruct (regular_subtyping H1) as [HWfEnv [HLcS HLcSel]]. 
*)



Lemma expands_sub_safe : forall E s S TMid DS q1 q2, E |== s -> (E, s) |= S ~<: TMid @ q1 -> (E, s) |= TMid ~< DS @ q2 -> exists q3, (E, s) |= S ~< DS @ q3.
Proof. Admitted. (* TODO *)



Lemma invert_typing_lam : forall E S t U q s, E |== s -> (E, s) |=  ok -> (E, s) |= lam S t ~: U @ q -> 
      exists q1, exists L, exists T, (forall x, x \notin L -> (ctx_bind (E, s) x S) |= (t ^^ x) ~: T @ q1) /\
      wf_tp (E, s) (tp_fun S T) /\ lc_tp T /\
      exists q2, (E, s) |= (tp_fun S T) ~<: U @ q2.
Proof. Admitted. (* TODO *)

Lemma invert_typing_sel: forall E t l T q s, E |== s -> (E, s) |=  ok -> (E, s) |= sel t l ~: T @ q ->   
      exists T', exists q1, (E, s) |= t ~: T' @ q1 /\
      exists DS, exists q2, (E, s) |= T' ~< DS @ q2 /\
      exists D, lbl.binds l D DS /\
      exists S, open_decl_cond D t (decl_tm S) /\
      exists q3, (E, s) |= S ~<: T @ q3.
Proof.
  introv. intros Hstowf Hok H. dependent induction H. 
    repeat eexists; eauto. 
    destruct (regular_expands H0) as [HWfE HLcT].
    apply sub_tp_refl; auto.
      admit. (* lc_tp T where T is in opened decl *)

    destruct (IHtyping s l t E); auto. exists x. 
    destruct H1 as [q1' [HT [DS [q2' [HX [D [Hin [S0 [HOpen [q3 HSub]]]]]]]]]].
    repeat ((eapply sub_tp_trans_safe; eauto) || (esplit; eauto)).
Qed.

Lemma invert_typing_ref: forall E s a T q, (E, s) |= ref a ~: T @ q -> 
    exists T', exists args, binds a (T', args) s /\
    exists q, (E, s) |= T' ~<: T @ q.
Proof. Admitted. (* TODO *)


Lemma invert_wf_store_uniq : forall s, wf_store s -> uniq s.
Proof. Admitted. (* TODO *)

Lemma invert_red_store_dom : forall s t t' s', s |~ t ~~> t' ~| s' -> dom s [<=] dom s'.
Proof. Admitted. (* TODO *)


(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "../metalib") ***
*** End: ***
*)  