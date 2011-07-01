Set Implicit Arguments.
Require Import List.
Require Import syntax_binding theory.
Require Import Metatheory LibTactics_sf support.
Require Import meta_pres_subst meta_weakening meta_inversion meta_binding meta_regular meta_decls meta_quality meta_path_eq.
Require Import Coq.Program.Equality.


Section Preservation.
(* mostly reusable boilerplate for the mutual induction: *)
  Let P0_ (E_s: env) (q: quality) (t: tm) (T: tp) (H: E_s |=  t ~: T  @ q) := forall E t' s s', E_s = (E, s) -> 
      E |== s -> E_s |= ok ->
      s  |~  t ~~> t'  ~| s' -> (E |== s' /\ exists q', (E, s') |=  t' ~: T @ q').  
  Let P1_ (E : env) (q : quality) (T : tp) (DS : decls) (H: E |= T ~< DS @ q) := True.
  Let P2_ (E : env) (q : quality) (T T' : tp) (H: E |= T ~<: T' @ q) := True.
  Let P3_ (e : env) (q : quality) (d d0 : decl) (H: sub_decl e q d d0) := True.
  Let P4_ (e : env) (t t0 : tm) (H: path_eq e t t0) := True.
  Let P5_ (e : env) (H: wf_env e) := True.
  Let P6_ (e : env) (t : tp) (H: wf_tp e t) := True.
  Let P7_ (e : env) (d : decl) (H: wf_decl e d) := True.
Lemma preservation : preservation. 
Proof. unfold preservation. 
  mutind_typing P0_ P1_ P2_ P3_ P4_ P5_ P6_ P7_; try solve [intros until s'; intros _ _ _ HRed; inverts HRed | idtac ].
  (*sel*) intros H IH HT'X _ Hin HopenD. (*presintros*) introv ? HStoTp ?(*H1*) HRed. subst.
    inverts HRed as. 
    SCase "red_sel". introv Hsto_wf Ha_in_sto HInArgs Hl_in_args. 
      split; auto.  rename t' into v. clear IH.

(* invert store typing to get well-formedness of the selected constructor argument *)
      inversion HStoTp as [_ Hsto_tp']. 
      destruct (Hsto_tp' a Tc ags Ha_in_sto) as [ags0 [HAgsEq [HTcConc [HDupA [DS0 [HTcX [HSameDomAgsDecls [L Hwf_args]]]]]]]]. clear Hsto_tp'.
      pick fresh x for L. set (Hwf_args x Fr) as Hwfargs.  subst.

(* XXX TODO
  H : (E0, s') |= ref a ~: T' @ q1
destruct (invert_typing_ref E0 s' a T' q1 H) as [Ta [ags' [Ha_in_sto' [qa HSubTa]]]]
  Ha_in_sto' : binds a (Ta, ags') s'
  HSubTa : (E0, s') |= Ta ~<: T' @ q

  Hsto_wf : wf_store s'
  Ha_in_sto : binds a (Tc, ags0 ^args^ ref a) s'
set binds_uniq_wf_store (Ha_in_sto' Ha_in_sto Ha_in_sto). subst.

  HSubTa : (E0, s') |= Tc ~<: T' @ q
  HT'X : (E0, s') |= T' ~< DS @ q2
apply expands_sub_safe
  HTcX : (E0, s') |= Tc ~< DS @ (q & q2)
  HTcConc : concrete Tc
  Hin : lbl.binds l D DS
destruct invert_expands_concrete
  HTcX' : (E0, s') |= Tc ~< DS' @ precise
  sub_decls DS' DS

  HTcX : (E0, s') |= Tc ~< DS0 @ precise
destruct expands_precise_concrete_unique

  DS' = DS0

  sub_decls DS0 DS
  Hin : lbl.binds l D DS
apply sub_decls_pres_binds

  Hin0 : lbl.binds l D' DS0
  sub_decl D' D
*)

      assert (exists D', lbl.binds l D' DS0 /\ exists q, sub_decl (E0, s') q D' D) as [D' [Hin' [qd HSubD]]].
      destruct (invert_typing_ref H) as [Ta [ags' [Ha_in_sto' [qa HSubTa]]]].
      set (binds_unique _ a (Tc, ags0 ^args^ ref a) (Ta, ags') s' Ha_in_sto Ha_in_sto' (invert_wf_store_uniq Hsto_wf)) as HH. injsubst HH.
      assert ( exists q3, (E0, s') |= Ta ~< DS @ q3) as HTaX by (eapply expands_sub_safe; eauto).
      destruct HTaX as [qxta HTaX].
      destruct (invert_expands_concrete HTaX HTcConc) as [DSa [HXTaP [qsdp Hsubdecls]]].
      assert ((E0, s') |= DS0 <:DS<: DS) as HSubDecls by (eapply quality_soundness; eauto).
(*
Hin : lbl.binds l D DS
HSubDecls : (E0, s') |= DS0 <:DS<: DS
====
Hin : lbl.binds l D' DS0
sub_decl D' D
*)
      destruct HSubDecls as [qsd HSubDecls]. 
      destruct (sub_decls_pres_binds l D Hin HSubDecls) as [D0 [qsd0 [Hin0 HSubD0]]].
      exists D0. splits; eauto.
      destruct (Hwfargs l D' Hin') as [_ HWfD0]. unfold open_decl in HWfD0. 

(* figure out what the declaration's type was opened to: replace D by decl_tm ?? *)
      inverts HopenD as; intros Hapath HDopena; [auto | destruct Hapath; apply path_ref]. induction D; inverts HDopena. inverts HSubD. simpl in HWfD0. rename t into T. 

      
(* finally get at the typing judgment for the declaration *)      
      destruct (HWfD0 ({0 ~tp> x}T1) eq_refl) as [v' [HInArgs' [_ HWfDTp]]]. change ({0 ~tp> x}T1) with (T1 ^tp^ x) in HWfDTp. clear HWfD0. subst.
 
(* commute opening with label lookup *)
(*
  HDupA   : lbl.uniq ags0
  HInArgs : lbl.binds l t' (lbl.map (open_rec_tm 0 a) ags0)
  HInArgs': lbl.binds l v' ags0
*)
      assert (v = ({0 ~> (ref a)}v')) by (eapply lbl.binds_unique; eauto; [
      unfold open_args; apply (lbl.binds_map_2 tm tm (open_rec_tm 0 (ref a)) l v' ags0 HInArgs') |
      apply lbl.uniq_map_2; eauto]). subst.
      change ({0 ~> (ref a)}v') with (v' ^^ (ref a)). change ({0 ~tp> (ref a)}T) with (T ^tp^ (ref a)).


(*
   H4 : (E0, s') |= T1 ~<: T @ qd
subtyping_regular
open_lc_is_noop
*)
   destruct (regular_subtyping H5) as [_ [HLcT1 HLcT]].
   rewrite (@open_lc_is_noop T1 x HLcT1) in H5. rewrite (@open_lc_is_noop T x HLcT) in H5.

(* apply the substitution lemma

  HWfDTp : exists q, ctx_bind E x Tc |= v' ^ x ~: T ^tp^ x @ q
  ============================
  exists q', E |= v' ^^ a ~: T ^tp^ a @ q'
*)

      apply subst_pres_typing with (x := x) (Tx := Tc); [ 
        destruct HWfDTp; eexists; eapply typing_sub; eauto |
        eauto |
        destruct (regular_expands HTcX) as [HWfE HLcTc]; eexists; eapply typing_ref; eauto]. 
        eapply weakening_subtyping; eauto. simpl. fsetdec.

   SCase "red_sel_tgt". rename t into t0. rename e' into t0'. 
      intros Hred0. destruct (@IH E0 t0' s s' eq_refl HStoTp H1 Hred0) as [Hsto_tp' [q1' H']].
      split; auto.
      exists (q1' & q2).
     
      (* recreate typing judgement for reduced subterm: apply typing_sel to typing judgement from IH, re-use old expansion *)

      inverts HopenD. (* was the self variable replaced by t0 in the typing judgement before reduction? *)
          assert ((E0, s') |=ok) as H1' by admit. (* by apply weakening_ctxok_store: H1 says (E0, s) |=ok *)
          assert (path t0'). eapply (red_pres_path Hsto_tp' H1' H4 Hred0); eauto. 
            eapply weakening_expansion_store; eauto. eapply invert_red_store_dom; eauto.
            unfold not. intros HDSnil. induction DS; eauto. inversion HDSnil. (* DS <> nil from In D DS*)

        (* yep, prove path equivalence t0 == t0' and apply typing_peq *) 
        induction D; unfold open_decl in H0; simpl in H0; inverts H0. rename t into T. change ({0 ~tp> t0}T) with (T ^tp^ t0).

          assert ((E0, s') |= sel t0' l ~: T ^tp^ t0' @ q1' & q2). 
          apply typing_sel with (T' := T') (D := (decl_tm T)) (DS := DS); try assumption.
          eapply weakening_expansion_store; eauto. eapply invert_red_store_dom; eauto.


          apply open_decl_path; auto.
(*   
   Hred0 : s |~ t0 ~~> t0' ~| s'
   path t0
   H' : E' |= t0' ~: T' @ q1'
   HT'X : E |= T' ~< DS @ q2
   DS <> nil
   ====== red_pres_path
   t0' path
*)

          replace (q1' & q2) with  ((q1' & q2) & precise).
          eapply (typing_sub H0); eauto. eapply sub_tp_path_eq; eauto. 
          
(*   Hred0 : s |~ t0 ~~> t0' ~| s'
   path t0
   path t0'
   Hsto_tp' : E' |== s'
   ====== red_implies_peq
   peq E' t0 t0'
*)
          admit. admit. (* lc_tp T, lc_tm t0'*)
          eapply red_implies_peq; eauto.

          induction qconj; eauto.

        (* nope *)
        apply typing_sel with (T' := T') (D := (decl_tm T)) (DS := DS); auto.
          eapply weakening_expansion_store; eauto. eapply invert_red_store_dom; eauto.
          apply open_lc_decl_ident; assumption.

  (*sub*) intros HT IHT HSub _. (*presintros*) introv ? HStoTp HBoundTOk HRed. subst. destruct (IHT E0 t' s s' eq_refl HStoTp HBoundTOk HRed) as [HStoTp' HT']. 
    inversion HT' as [q' HT'']. split; try assumption. 
    eexists. eapply typing_sub; eauto. eapply weakening_subtyping_store; eauto; eapply invert_red_store_dom; eauto.

  (*app*) intros HTFun IHTFun HTArg IHTArg. (*presintros*) introv ? HStoTp HBoundTOk HRed. subst. inverts HRed.
    SCase "red_beta". split; auto. clear IHTArg IHTFun.
      destruct (invert_typing_lam HStoTp HBoundTOk HTFun) as [q0 [L [Tr' [HT [HWf [HLcT [? Hsubfun]]]]]]]. 
      destruct (invert_subtyping_fun) as [_ InvSubFun]. (* THIS IS WHAT BRINGS ON THE HURT *)
      assert (exists T1', exists T2', subsumes_fun_tp (tp_fun Ta Tr) T1' T2' 
                /\ (exists q, (E0, s') |= T1' ~<: T @ q 
                /\ (exists q0, (E0, s') |= Tr' ~<: T2' @ q0))) as [T1' [T2' [HSFT [qa [HSubArg [qr HSubRes]]]]]]. 
        eapply (InvSubFun (E0, s') x (tp_fun T Tr') (tp_fun Ta Tr)  Hsubfun); eauto.
        unfold not. intros. inverts H. (* urgh... *)
     inverts HSFT.

     assert (exists q, (E0, s') |= t ^^ ta ~: Tr' ^tp^ ta @ q).
      pick fresh z for L. set (HT z Fr) as HT'. 
      apply subst_pres_typing with (x := z) (Tx := T); eauto. 
      replace (Tr' ^tp^ z) with (Tr'); [idtac | apply open_lc_is_noop; eauto]. eexists; eauto.
      eexists; eapply typing_sub; eauto.
    replace (Tr' ^tp^ ta) with (Tr') in H; [idtac | apply open_lc_is_noop; eauto]. 
    destruct H. eexists; eapply typing_sub; eauto.

    SCase "red_app_fun".
      destruct (IHTFun E0 e' s s' eq_refl HStoTp HBoundTOk H5) as [? [qf' HTFun']].
      split; auto. exists qf'. 
        assert (exists q, (E0, s') |= ta ~: Ta @ q) as [qa HTa] by (eapply weakening_typing_store; eauto; eapply invert_red_store_dom; eauto).
        eapply typing_app; eauto.

    SCase "red_app_arg".
      destruct (IHTArg E0 e' s s' eq_refl HStoTp HBoundTOk H5) as [? [qa' HTArg']].
      split; auto. 
        assert (exists q, (E0, s') |= tf ~: tp_fun Ta Tr @ q) as [qf HTf] by (eapply weakening_typing_store; eauto; eapply invert_red_store_dom; eauto).
        exists qf. eapply typing_app; eauto.

  (* new *) intros HWfTc _ HConcTc HTcX _ HArgsUniq HDomDsEqArgs HArgsWf HT IHt. (*presintros*) introv ? HStoTp HBoundTOk HRed. subst. inverts HRed.
   destruct (regular_expands HTcX) as [HWfE HLcTc].
   split. 
     SCase "extended store is well-typed in extended env".
     unfold typing_store. Focus. splits.
       apply wf_store_cons_tp; auto.
(*
TP:
  HArgsUniq : lbl.uniq args
  H7 : forall (v' : tm), lbl.binds l v' args -> value (v' ^^ ref a)
  H : lbl.binds l v (args ^args^ ref a)
  =====
  value v

remember (open_rec_tm 0 (ref a)) as f. 

  f = {0 -> (ref a)}
  HArgsUniq : uniq args
  H7 : forall v', binds l v' args -> value (f v')
  H : binds l v ((map f) args)
  =====
  value v

  H : binds l v ((map f) args)

destruct (binds_map_3 H) as [v' H']

  H': binds l v' args

set (binds_map_2 f H') as H''

  H'': binds l (f v') ((map f) args)

set (binds_unique H H'' HArgsUniq) as Heqvv'

  Heqvv' : v = (f v')

rewrite Heqvv'

rewrite Heqf. apply H7 with (l := l); auto.

*)

     intros. unfold open_args in H. remember (open_rec_tm 0 (ref a)) as f. 
     destruct (binds_map_3 l v f args H) as [v' H'].
     set (lbl.binds_map_2 tm tm f l v' args H') as H''.
     set (lbl.binds_unique tm l v (f v') (lbl.map f args) H H'' (lbl.uniq_map_2 tm tm f args HArgsUniq)) as Heqvv'.
     rewrite Heqvv'.
     rewrite Heqf. apply H7 with (l := l); auto.

     (* split off the new binding, the rest of the store is ok by HStoTp *)
       simpl. introv. rewrite binds_cons_iff. apply or_ind; revert a0 Tc0 argsRT.
       (* the new binding *) introv [HEq HEq']. subst. injsubst HEq'. Focus.
       exists args. splits; eauto. exists ds. split.
       eapply weakening_expansion_store; eauto. simpl. fsetdec.
       split; auto.
       exists L. intros x Fr. introv HBindsL. destructs (HArgsWf x Fr l d HBindsL).
       split.
         intros. destruct (H U T0 H1). eexists; eapply weakening_subtyping_store; eauto. simpl. fsetdec.
         intros. destruct (H0 T0 H1). destruct H3 as [HBinds [HVal [qx HTx]]]. exists x0. splits; eauto. 
         eapply weakening_typing_store; [eauto | eapply HTx]. simpl. fsetdec.
       (* invert HStoTp and apply weakening_???_store *)
       introv Ha_in_sto. 
      inversion HStoTp as [_ Hsto_tp']. destruct (Hsto_tp' a0 Tc0 argsRT Ha_in_sto) as [ags0 [HAgsEq [HTcConc [HDupA [DS0 [HTcX' [HSameDomAgsDecls [L' Hwf_args]]]]]]]]. 
      exists ags0. splits; eauto. exists DS0. split.
       eapply weakening_expansion_store; eauto. simpl. fsetdec.
       split; auto.
       exists L'. intros x Fr. introv HBindsL. destructs (Hwf_args x Fr l d HBindsL).
       split.
         intros. destruct (H U T0 H1). eexists; eapply weakening_subtyping_store; eauto. simpl. fsetdec.
         intros. destruct (H0 T0 H1). destruct H3 as [HBinds [HVal [qx HTx]]]. exists x0. splits; eauto. 
         eapply weakening_typing_store; [eauto | eapply HTx]. simpl. fsetdec.

     SCase "opening up the body with (ref a) is well-typed in E'".
       pick fresh x for L. set (HT x Fr) as HTAss0.
       destruct (regular_typing HTAss0) as [HWFE [_ HLcT]].
       assert (exists q,  ctx_bind (E0,  [(a, (Tc, args ^args^ ref a))] ++ s) x Tc |= t ^ x ~: T @ q) as HTpAss. eapply weakening_typing_store; eauto.  simpl. fsetdec. 
       replace (T) with (T ^tp^ x) in HTpAss; [idtac | rewrite <- open_lc_is_noop; eauto].
       replace (T) with (T ^tp^ (ref a)); [idtac | rewrite <- open_lc_is_noop; eauto]. 
       apply subst_pres_typing with (x := x) (Tx := Tc); eauto. 
       eexists; eapply typing_ref; eauto.
       eapply weakening_wf_env_store; eauto.
Qed.

End Preservation.

(*
   unfold typing_store.

   set (E' := ( a ~ Tc ++ fst E, extract_pex a args ++ snd E)).
   assert (dom (fst E)[<=]dom (fst E')) by (simpl; fsetdec).
   assert (wf_env E') as HWfE'. 
     eapply wf_env_; eauto. eapply wf_ctx_cons_tp; eauto. 
       rewrite <- H3. simpl. auto. 
       inversion HStoTp as [_ [HDomEnvStoEq _]]. fsetdec.
       admit. (* forall x : atom, x `notin` dom (fst E) -> x `notin` fv_tp Tc *)
       inversion HStoTp. rewrite <- H3. simpl. auto. admit.

  wf_store s
  forall (l : label) (v : tm), lbl.binds l v args -> value (v ^^ ref a)
  a `notin` dom s
  wf_pex G P
  dom G [=] dom s
  
  (forall (a : atom) (Tc : tp) (args' : syntax_binding.args)
      (ds : decls),
    binds a (Tc, args') s ->
    exists args0,
    args' = args0 ^args^ ref a /\
    Forall (pex_has (G, P)) (extract_pex a args0))
 ============================
   wf_pex ((a, Tc) :: G) (extract_pex a args ++ P)

   exists E'. 
     split; [idtac | split; [simpl; fsetdec | idtac]].

*)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "../metalib") ***
*** End: ***
*)  