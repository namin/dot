Set Implicit Arguments.
Require Import List.
Require Import syntax_binding theory.
Require Import Metatheory LibTactics_sf support.
Require Import meta_pres_subst meta_weakening meta_inversion.
Require Import Coq.Program.Equality.


Lemma open_lc_decl_ident: forall d t, lc_decl d -> open_decl_cond d t d. Admitted.


Lemma red_pres_path: forall s t t' s' E' T q DS q', 
  E' |== s' -> path t -> s |~ t ~~> t' ~| s' -> E' |= t' ~: T @ q -> E' |= T ~< DS @ q' -> DS <> nil
    -> path t'.
Proof.
  introv HStoTp Hpath Hred Htp HX. generalize dependent q'. generalize dependent q. generalize dependent T. generalize dependent DS. induction Hred; intros; inverts Hpath; eauto. inverts H2 (*value v*); auto.

  destruct (invert_typing_lam HStoTp Htp) as [? [? [? [? [? [? HSubFun]]]]]]. 
  set (expands_sub_safe HStoTp HSubFun HX) as HXF. destruct HXF as [qq HXF']. set (invert_expands_fun HXF'). tauto.
  apply path_sel. 

  destruct (invert_typing_sel HStoTp Htp) as [T' [q1 [HT [DS' [q2 [HX' [D [HIn [S [Hopen [q3 HSub]]]]]]]]]]].
  eapply IHHred; eauto. unfold not. intros. induction DS'; eauto. inversion H0.
Qed.


Section Preservation.
(* mostly reusable boilerplate for the mutual induction: *)
  Let P0_ (E: env) (q: quality) (t: tm) (T: tp) (H: E  |=  t ~: T  @ q) := forall t' s s', 
    E  |== s -> s  |~  t ~~> t'  ~| s' ->
      (exists E', 
        E' |== s' 
          /\ dom (fst E) [<=] dom (fst E') 
          /\ exists q', E' |=  t' ~: T @ q').
  Let P1_ (E : env) (q : quality) (T : tp) (DS : decls) (H: E |= T ~< DS @ q) := True.
  Let P2_ (E : env) (q : quality) (T T' : tp) (H: E |= T ~<: T' @ q) := True.
  Let P3_ (e : env) (q : quality) (d d0 : decl) (H: sub_decl e q d d0) := True.
  Let P4_ (e : env) (t t0 : tm) (H: path_eq e t t0) := True.
  Let P5_ (e : env) (H: wf_env e) := True.
  Let P6_ (c : ctx) (H: wf_ctx c) := True.
  Let P7_ (c : ctx) (p : pex) (H: wf_pex c p) := True.
  Let P8_ (e : env) (t : tp) (H: wf_tp e t) := True.
  Let P9_ (e : env) (d : decl) (H: wf_decl e d) := True.
Lemma preservation : preservation. 
Proof. unfold preservation. 
  mutind_typing P0_ P1_ P2_ P3_ P4_ P5_ P6_ P7_ P8_ P9_.
  (*var*) intros ? ? ? ? ? ? ? ? Hred. inversion Hred.
  (*ref*) intros ? ? ? ? ? ? ? ? Hred. inversion Hred.
  (*sel*) intros H IH HT'X _ Hin HopenD. introv Hsto_tp Hred.
    inverts Hred as. 
    SCase "red_sel". introv Hsto_wf Ha_in_sto HInArgs Hl_in_args.
      exists E. splits; [eauto | unfold AtomSetImpl.Subset; eauto | idtac]. (* store doesn't change*)

(* invert store typing to get well-formedness of the selected constructor argument *)
      inverts Hsto_tp as. intros _ [HEnvStoDom Hsto_tp']. 
      destruct (Hsto_tp' a Tc ags DS Ha_in_sto) as [ags0 [HAgsEq [HXPex [HTcConc [HAtpTc [HTcX [L Hwf_args]]]]]]]. clear Hsto_tp'.
      pick fresh x for L. set (Hwf_args x Fr) as Hwfargs. inverts Hwfargs as. intros HDupA [HSameDomAgsDecls Hwf_args']. clear Hwf_args. subst.
      destruct (Hwf_args' l D Hin) as [_ HWfD0]. unfold open_decl in HWfD0. 

(* figure out what the declaration's type was opened to: replace D by decl_tm ?? *)
      inverts HopenD as; intros Hapath HDopena; [auto | destruct Hapath; apply path_ref]. induction D; inverts HDopena. simpl in HWfD0. 

(* finally get at the typing judgment for the declaration *)      
      destruct (HWfD0 ({0 ~tp> x}t) eq_refl) as [v' [HInArgs' [_ HWfDTp]]]. change ({0 ~tp> x}t) with (t ^tp^ x) in HWfDTp. clear Hwf_args' HWfD0.
 
(* commute opening with label lookup *)
(*
  HDupA   : LabelMapImpl.uniq ags0
  HInArgs : LabelMapImpl.binds l t' (LabelMapImpl.map (open_rec_tm 0 a) ags0)
  HInArgs': LabelMapImpl.binds l v' ags0
*)
      assert (t' = ({0 ~> (ref a)}v')) by (eapply LabelMapImpl.binds_unique; eauto; [
      unfold open_args; apply (LabelMapImpl.binds_map_2 tm tm (open_rec_tm 0 (ref a)) l v' ags0 HInArgs') |
      apply LabelMapImpl.uniq_map_2; eauto]). subst.
      change ({0 ~> (ref a)}v') with (v' ^^ (ref a)). change ({0 ~tp> (ref a)}t) with (t ^tp^ (ref a)). rename t into T.

(* apply the substitution lemma

  HWfDTp : exists q, ctx_bind E x Tc |= v' ^ x ~: T ^tp^ x @ q
  ============================
  exists q', E |= v' ^^ a ~: T ^tp^ a @ q'
*)
      apply subst_pres_typing with (x := x) (Tx := Tc); eauto.

   SCase "red_sel_tgt". rename t into t0. rename e' into t0'. 
      intros Hred0. set (@IH t0' s s' Hsto_tp Hred0) as HH. destruct HH as [E' [Hsto_tp' [Hdom [q1' H']]]].
      exists E'. splits; auto.
      exists (q1' & q2).
     
      (* recreate typing judgement for reduced subterm: apply typing_sel to typing judgement from IH, re-use old expansion *)

      inverts HopenD. (* was the self variable replaced by t0 in the typing judgement before reduction? *)
        (* yep, prove path equivalence t0 == t0' and apply typing_peq *) 
        induction D; unfold open_decl in H0; simpl in H0; inverts H0. rename t into T. change ({0 ~tp> t0}T) with (T ^tp^ t0).

          assert (E' |= sel t0' l ~: T ^tp^ t0' @ q1' & q2). 
          apply typing_sel with (T' := T') (D := (decl_tm T)) (DS := DS); try assumption.
          apply weakening_expansion with (E := E); assumption. 
          apply open_decl_path. 
(*   
   Hred0 : s |~ t0 ~~> t0' ~| s'
   path t0
   H' : E' |= t0' ~: T' @ q1'
   HT'X : E |= T' ~< DS @ q2
   DS <> nil
   ====== red_pres_path
   t0' path
*)
          eapply (red_pres_path Hsto_tp' H3 Hred0); eauto.
            apply weakening_expansion with (E := E); eauto. 
            unfold not. intros HDSnil. induction DS; eauto. inversion HDSnil. (* DS <> nil from In D DS*)

          replace (q1' & q2) with  ((q1' & q2) & precise).
          eapply (typing_sub H0 (sub_tp_path_eq T _)); try assumption. induction qconj; eauto.
(*   Hred0 : s |~ t0 ~~> t0' ~| s'
   path t0
   path t0'
   Hsto_tp' : E' |== s'
   ====== red_implies_peq
   peq E' t0 t0'
*)
        (* nope *)
        apply typing_sel with (T' := T') (D := (decl_tm T)) (DS := DS); auto; [
          apply weakening_expansion with (E := E); assumption |
          apply open_lc_decl_ident; assumption].

  (*sub*) intros HT IHT HSub _. introv. intros HStoTp HRed. destruct (IHT t' s s' HStoTp HRed) as [E' [HStoTp' [HDom HT']]]. 
    exists E'. inversion HT' as [q' HT'']. split; try assumption. split; try assumption.
    eexists. eapply typing_sub; eauto. eapply weakening_subtyping; eauto.

Focus.

  (*app*) intros HTFun IHTFun HTArg IHTArg. introv. intros HStoTp HRed. inverts HRed.
    SCase "red_beta". exists E. split; auto. split; auto. unfold AtomSetImpl.Subset. auto. clear IHTArg IHTFun.
      destruct (invert_typing_lam HStoTp HTFun) as [q0 [L [Tr' [HT [HWf [? Hsubfun]]]]]]. 

(*

  E |= tp_fun T Tr' ~<: U @ q
  ============================ invert_subtyping_fun
  E |= U ~<: tp_fun T Tr' @ q
  E |= Ta <: T /\   E |= Tr' <: Tr

  E |== s
  Hsubfun : E |= tp_fun T Tr' <: tp_fun Ta Tr @ x
  ============================ invert_subtyping_fun
  E |= Ta <: T /\   E |= Tr' <: Tr

  HTArg : E |= ta ~: Ta @ q'
  ===== typing_sub
  E |= ta ~: T @ q''

  HT : forall x : atom, x `notin` L -> ctx_bind E x T |= t ^^ x ~: Tr' @ q0
  === pick fresh x for HT
  ctx_bind E x0 T |= t ^ x0 ~: Tr' @ q0
  
  H6 : value ta
  E |= ta ~: T @ q''
  ===== subst_pres_typing
  E |= t ^^ ta ~: Tr' @ q0
  
  E |= Tr' <: Tr
  ===== typing_sub
  E |= t ^^ ta ~: Tr @ q0'

  s' : store
  T : tp
  t : tm
  H1 : wf_store s'
  H3 : lc_tm (lam T t)
  HStoTp : E |== s'
*)
 
    SCase "red_app_fun".

    SCase "red_app_arg".

destruct (IHT t' s s' HStoTp HRed) as [E' [HStoTp' [HDom HT']]]. 
  

End Section.

(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "../metalib") ***
*** End: ***
*)  