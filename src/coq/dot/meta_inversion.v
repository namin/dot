Set Implicit Arguments.
Require Import List.
Require Import syntax_binding theory.
Require Import Metatheory LibTactics_sf support meta_regular meta_binding.
Require Import Coq.Program.Equality.


(*
Reserved Notation "E |= T1 ~<^ T2" (at level 69).

(* chase type member selections up *)
Inductive promote : env -> tp -> tp -> Prop :=
  | promote_upper : forall E p T' DS L S U T,
      E |= p ~: T' @ precise -> E |= T' ~< DS @ precise -> lbl.binds L (decl_tp S U) DS -> (*      path p -> for regularity *)
      E |= (U ^tp^ p) ~<^ T ->
      E |= (tp_sel p L) ~<^ T 
  | promote_lower : forall E p T' DS L S U T,
      E |= p ~: T' @ precise -> E |= T' ~< DS @ precise -> lbl.binds L (decl_tp S U) DS -> (*      path p -> for regularity *)
      E |= (U ^tp^ p) ~<^ T ->
      E |= (S ^tp^ p) ~<^ T
  | promote_refl : forall E T,
      (forall p L, T <> (tp_sel p L)) ->
      E |= T ~<^ T 
      
where "E |= T1 ~<^ T2" := (promote E T1 T2).

  Let P1_ (E : env) (q : quality) (T : tp) (DS : decls) (H: E |= T ~< DS @ q) := True. (*exists T1, exists T2, subsumes_fun_tp T T1 T2 -> DS = nil.*)
  Let P2_ (E : env) (q : quality) (T T' : tp) (H: E |= T ~<: T' @ q) := 
      (exists p, exists L,   T' = tp_sel p L   -> forall U,     E |= T' ~<^ U -> E |= T ~<^ U) /\
      (exists S2, exists T2, T' = tp_fun S2 T2 -> forall S1 T1,                  E |= T ~<^ tp_fun S1 T1 -> exists q1, exists q2, E |= S2 ~<: S1 @ q1 /\ E |= T1 ~<: T2 @ q2).

  mutind_typing P0_ P1_ P2_ P3_ P4_ P5_ P6_ P7_; intros; split; try solve [ repeat eexists; discriminate ].
  repeat eexists. intros. rewrite -> H0 in *.
Show 5.
*)

Inductive subsumes_fun_tp : tp -> tp -> tp -> Prop :=
 | sf_top : subsumes_fun_tp (tp_top) tp_bot tp_top
 | sf_fun : forall S T, subsumes_fun_tp (tp_fun S T) S T
 | sf_and : forall S T S' T' T1 T2, subsumes_fun_tp T1 S T -> subsumes_fun_tp T2 S' T'-> subsumes_fun_tp (tp_and T1 T2) (tp_or S S') (tp_and T T')
 | sf_or1 : forall S T T1 T2, subsumes_fun_tp T1 S T -> subsumes_fun_tp (tp_or T1 T2) S T
 | sf_or2 : forall S T T1 T2, subsumes_fun_tp T2 S T -> subsumes_fun_tp (tp_or T1 T2) S T.

Hint Constructors subsumes_fun_tp.



Section InvSubFun.
  Let P0_ (E: env) (q: quality) (t: tm) (T: tp) (H: E  |=  t ~: T  @ q) := True.
  Let P1_ (E : env) (q : quality) (T : tp) (DS : decls) (H: E |= T ~< DS @ q) := exists T1, exists T2, subsumes_fun_tp T T1 T2 -> DS = nil.
  Let P2_ (E : env) (q : quality) (T T' : tp) (H: E |= T ~<: T' @ q) := forall T1 T2, subsumes_fun_tp T T1 T2 -> ~ has_tp_sel T' -> exists T1', exists T2', subsumes_fun_tp T' T1' T2' /\ exists q, E |= T1' ~<: T1 @ q /\ exists q, E |= T2 ~<: T2' @ q.
  Let P3_ (e : env) (q : quality) (d d0 : decl) (H: sub_decl e q d d0) := True.
  Let P4_ (e : env) (t t0 : tm) (H: path_eq e t t0) := True.
  Let P5_ (e : env) (H: wf_env e) := True.
  Let P6_ (e : env) (t : tp) (H: wf_tp e t) := True.
  Let P7_ (e : env) (d : decl) (H: wf_decl e d) := True.

(* this is the first lemma that i tried to prove that relies on E only having x : T for which T has been checked for full well-formedness, as performed by typing_new  *)
Lemma invert_subtyping_fun : 
   (forall E q T DS, E |= T ~< DS @ q -> exists T1, exists T2, subsumes_fun_tp T T1 T2 -> DS = nil) /\
   (forall E q T T', E |= T ~<: T' @ q -> forall T1 T2, subsumes_fun_tp T T1 T2 -> ~ has_tp_sel T' -> exists T1', exists T2', subsumes_fun_tp T' T1' T2' /\ exists q, E |= T1' ~<: T1 @ q /\ exists q, E |= T2 ~<: T2' @ q).
Proof. Admitted.


(*
Lemma invert_subtyping_and_l : forall E T1 T2 T q, E |= tp_and T1 T2 ~<: T @ q -> 
  (exists q, E |= T1 ~<: T @ q) /\ (exists q, E |= T2 ~<: T @ q).
Proof. Admitted.

  mutind_typing P0_ P1_ P2_ P3_ P4_ P5_ P6_ P7_; intros; try solve [ eauto ].

Lemma invert_subtyping_fun: forall E S T U S' T' q1 q2 s,  E |== s ->
  E |= (tp_fun S T) ~<: U @ q1 -> E |= U ~<: (tp_fun S' T') @ q2 -> (~ has_tp_sel U) ->
  exists q1, sub_tp E q1 S' S /\ exists q2, sub_tp E q2 T T'.
Proof. introv. intros HStoTp HSubL. generalize dependent S'. generalize dependent T'. generalize dependent q2.
  dependent induction HSubL; introv; intros HSubR. (* first get all subgoals to shape  S -> T <: S' -> T' *)

    destruct T0; unfold open_tp in *; simpl in *; inverts x. intros. admit. (* peq *)
    admit. (* tp_fun does not expand*)
    intros. set (H2 p L) as HH. unfold not in HH. tauto. (* trans for tp_sel *)
    intros. assert (tp_fun S T = tp_fun S T); auto. set (@IHHSubL1 S T HStoTp H1 (q2 & q0) T'0 S' (sub_tp_trans H0 HSubL2 HSubR)). auto. (* ok trans: use IH *)
    intros. admit. (* refl *)
    intros. admit. (* fun -> do common thing, then use trans*)
    intros. destruct (invert_subtyping_and_l HSubR) as [HSub1 HSub2]. inverts HSub1. apply IHHSubL1 with (q2 := x); auto. admit. admit. admit. 
*)


End InvSubFun.

(* more convenient interface to above *)
Lemma invert_expands_fun: forall E S T DS q,  E |= tp_fun S T ~< DS @ q -> DS = nil.
Proof. Admitted.





  
Inductive subsumes_top : env -> tp -> Prop := 
 | st_top : forall E,  subsumes_top E tp_top
 | st_rfn : forall E T, subsumes_top E T -> subsumes_top E (tp_rfn T nil)
 | st_and : forall E T1 T2, subsumes_top E T1 -> subsumes_top E T2 -> subsumes_top E (tp_and T1 T2)
 | st_or1 : forall E T1 T2, subsumes_top E T1 -> subsumes_top E (tp_or T1 T2)
 | st_or2 : forall E T1 T2, subsumes_top E T2 -> subsumes_top E (tp_or T1 T2).

(*
 | st_sel_punt : forall E p L q,
  E |= tp_top ~<: (tp_sel p L) @ q ->
  subsumes_top E (tp_sel p L).
 | st_sel_lower : forall E p T' q1 DS q2 L S U,
  E |= p ~: T' @ q1 ->
  E |= T' ~< DS @ q2 ->
  lbl.binds L (decl_tp S U) DS ->
  path_safe E p ->
  subsumes_top E (S ^tp^ p) ->
  subsumes_top E (tp_sel p L)
 | st_sel_upper : forall E p T' q1 DS q2 L S U,
  E |= p ~: T' @ q1 ->
  E |= T' ~< DS @ q2 ->
  lbl.binds L (decl_tp S U) DS ->
  path p ->
  subsumes_top E (tp_sel p L) ->
  subsumes_top E (U ^tp^ p).*)

Hint Constructors subsumes_top.

(*
Lemma opening_pres_subsumes_top : forall E T p p', path_eq E p p' -> subsumes_top E (T ^tp^ p) -> subsumes_top E (T ^tp^ p'). 
Proof.
  introv. intros Hpeq H. unfold open_tp in *; simpl. induction T; try solve [inverts H; simpl; auto].
    simpl in *. inverts H. eapply st_sel; eauto.
    induction l. simpl. auto. inverts H2.
Qed.

Lemma and_decls_nil_2 : forall ds, and_decls nil nil ds -> ds = nil.
Proof. introv. intros.   unfold and_decls in H. destruct H as [_ [HDSOk1 [HDSOk2 H]]]. unfold iff in H. assert (forall (l : label) (d : decl),
      lbl.binds l d ds ->
      (exists d1 d2,
       lbl.binds l d1 nil /\
       lbl.binds l d2 nil /\ and_decl d1 d2 d) \/
      lbl.binds l d nil \/ lbl.binds l d nil) by apply H. clear H.
   induction ds; auto. destruct a. unfold lbl.binds in H0. destruct (H0 l d); simpl; auto.
   destruct H. destruct H. destruct H. destruct H. 
   destruct H. destruct H. destruct H. 
Qed.

Lemma or_decls_nil_2 : forall ds1 ds2 ds, or_decls ds1 ds2 ds -> ds1 = nil \/ ds2 = nil -> ds = nil.
Proof. Admitted.

Section InvSubTop.
  Let P0_ (E: env) (q: quality) (t: tm) (T: tp) (H: E  |=  t ~: T  @ q) := True.
  Let P1_ (E : env) (q : quality) (T : tp) (DS : decls) (H: E |= T ~< DS @ q) := subsumes_top E T -> DS = nil.
  Let P2_ (E : env) (q : quality) (T T' : tp) (H: E |= T ~<: T' @ q) := subsumes_top E T -> subsumes_top E T'.
  Let P3_ (e : env) (q : quality) (d d0 : decl) (H: sub_decl e q d d0) := True.
  Let P4_ (e : env) (t t0 : tm) (H: path_eq e t t0) := True.
  Let P5_ (e : env) (H: wf_env e) := True.
  Let P6_ (e : env) (t : tp) (H: wf_tp e t) := True.
  Let P7_ (e : env) (d : decl) (H: wf_decl e d) := True.

Lemma invert_subtyping_top : 
   (forall E q T DS, E |= T ~< DS @ q -> E |= T ~<^ T' -> subsumes_top E T -> DS = nil) /\
   (forall E q T T', E |= T ~<: T' @ q -> subsumes_top E T -> subsumes_top E T').
Proof. 
mutind_typing P0_ P1_ P2_ P3_ P4_ P5_ P6_ P7_; intros; try solve [inverts H;eauto | inverts H0;eauto | inverts H1;eauto | eauto ].

(*cases: *)
    (* expands_rfn *) inverts H0. assert (DSP = nil) by auto. subst. apply and_decls_nil_2; assumption.
    (* expands_and *) inverts H1. assert (DS1 = nil) by auto; assert (DS2 = nil) by auto. subst. apply and_decls_nil_2; assumption.
    (* expands_or *) assert (DS1 = nil \/ DS2 = nil) by (inverts H1; [left; auto | right; auto]). apply or_decls_nil_2 with (ds1 := DS1) (ds2 := DS2); assumption.
    (* sub_tp_rfn_intro *) assert (DS = nil) by auto. subst. inverts H0; auto. 
    (* sub_tp_rfn *) eauto. assert (DS2 = nil). inverts H. unfold LabelSetImpl.Subset in s. simpl in s. induction DS2; auto. destruct a. assert (LabelSetImpl.In l LabelSetImpl.empty). apply (s l). eapply (lbl.binds_In); eauto. LabelSetDecide.fsetdec. subst. inverts H. auto.
    (* sub_tp_rfn_precise *) inverts H0; auto.
      assert (DS2 = nil). unfold LabelSetImpl.Subset in e. simpl in e. induction DS2; auto. destruct a. simpl in e. unfold LabelSetImpl.Equal in e. unfold iff in e. destruct (e l) as [HF _]. assert ( LabelSetImpl.In l LabelSetImpl.empty). LabelSetDecide.fsetdec. rewrite (LabelSetFacts.empty_iff) in H0. contradiction H0. subst. auto.
    (* sub_tp_tpsel_lower *) 
    (* sub_tp_tpsel_upper *) 
    (* sub_tp_path_eq *) apply opening_pres_subsumes_top with (p := p'); auto.
Qed.
End InvSubTop.

assert (E |= (S ^tp^ p) ~<: (tp_sel p L) @ subsumed) by (eapply sub_tp_tpsel_lower; eauto). assert (exists q, E |= tp_top ~<: (S ^tp^ p) @ q) as HSubS by admit. destruct HSubS. eapply st_sel_punt. eapply sub_tp_trans; eauto.
assert (E |= (tp_sel p L) ~<: (U ^tp^ p) @ (q1 & q2)) by (eapply sub_tp_tpsel_upper; eauto). inverts H1 as HSubS. eapply st_sel_punt. eapply sub_tp_trans; eauto.
*)




Lemma invert_expands_concrete : forall E s Tc DS q, (E, s) |= Tc ~< DS @ q -> concrete Tc -> 
    exists DS', (E, s) |= Tc ~< DS' @ precise /\ exists q, sub_decls (E, s) q DS' DS.
Proof. Admitted.

Lemma invert_wf_store_uniq : forall s, wf_store s -> uniq s.
Proof. Admitted.


(* XXXX probably not provable as-is: what if E has an evil variable binding? that could be used to create an illegal subtyping derivation *)
Lemma sub_tp_trans_safe : forall E s S TMid T q1 q2, E |== s -> (E, s) |= S ~<: TMid @ q1 -> (E, s) |= TMid ~<: T @ q2 -> exists q3, (E, s) |= S ~<: T @ q3.
Proof. Admitted. (* intros.  set TMid as TMid'. destruct TMid; try solve [exists (q1 & q2); apply sub_tp_trans with (TMid := TMid'); auto; unfold not; intros ? ? HH; inversion HH | idtac]. clear TMid'.   dependent induction H0.*)

Lemma expands_sub_safe : forall E s S TMid DS q1 q2, E |== s -> (E, s) |= S ~<: TMid @ q1 -> (E, s) |= TMid ~< DS @ q2 -> exists q3, (E, s) |= S ~< DS @ q3.
Proof. Admitted.

Lemma invert_typing_lam : forall E S t U q s, E |== s -> (E, s) |= lam S t ~: U @ q -> 
      exists q1, exists L, exists T, (forall x, x \notin L -> (ctx_bind (E, s) x S) |= (t ^^ x) ~: T @ q1) /\
      wf_tp (E, s) (tp_fun S T) /\ lc_tp T /\
      exists q2, (E, s) |= (tp_fun S T) ~<: U @ q2.
Proof. Admitted.

Lemma invert_typing_sel: forall E t l T q s, E |== s -> (E, s) |= sel t l ~: T @ q ->   
      exists T', exists q1, (E, s) |= t ~: T' @ q1 /\
      exists DS, exists q2, (E, s) |= T' ~< DS @ q2 /\
      exists D, lbl.binds l D DS /\
      exists S, open_decl_cond D t (decl_tm S) /\
      exists q3, (E, s) |= S ~<: T @ q3.
Proof.
  introv. intros Hstowf H. dependent induction H. 
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
Proof. Admitted.


Lemma invert_red_store_dom : forall s t t' s', s |~ t ~~> t' ~| s' -> dom s [<=] dom s'.
Proof. Admitted.



(*
Lemma and_decls_nil : forall ds1 ds2, and_decls ds1 ds2 nil -> ds1 = nil /\ ds2 = nil.
Proof. introv. intros. 
  unfold and_decls in H. destruct H as [_ [HDSOk1 [HDSOk2 H]]]. assert (forall (l : label) (d : decl), (
      (exists d1 d2, lbl.binds l d1 ds1 /\ lbl.binds l d2 ds2 /\ and_decl d1 d2 d) \/
       lbl.binds l d ds1 \/ 
       lbl.binds l d ds2) -> lbl.binds l d nil). unfold iff in H. apply H.  clear H.  
        unfold lbl.binds in H0. simpl in H0. induction ds1; induction ds2; auto; destruct a. 
         destruct (H0 l d). right. right. simpl. left. auto.
         destruct (H0 l d). right. left. simpl. left. auto.
         destruct (H0 l d). right. left. simpl. left. auto.
Qed.


(*Lemma top_insensitive_opening : forall T p, subsumes_top T -> subsumes_top (T ^tp^ p). 
Proof.
  intros. induction H; auto; unfold open_tp in *; simpl; auto.
Qed.*)

(*Instance EqDec_eq_label : EqDec_eq label.
Proof. unfold EqDec_eq. decide equality; decide equality; eauto. Defined.

Set Implicit Arguments.
Lemma binds_map_3 : forall A B (x: label) (b: B) (f: A -> B) E,
  (forall a b, f a = f b -> a = b) ->
  lbl.uniq E ->
  lbl.binds x b (lbl.map f E) ->
  exists a, lbl.binds x a E /\ b = f a.
Proof.
  labelmap induction E; intros HFInjection HUniq HBTail.
    inversion HBTail. set (lbl.binds_map_1 B A f x b HBTail).
set (lbl.binds_app_uniq_1 B x b _ _ HUniq HBTail).
    unfold lbl.binds in *. simpl in *. destruct (x == x0); subst.
      inverts HUniq. exists a. split. left; auto. inverts HBTail; eauto. inverts H; auto.
      right. auto.
Qed.*)

Inductive not_lambda : tm -> Prop :=
| not_lambda_bvar : forall x, not_lambda (bvar x)
| not_lambda_fvar : forall x, not_lambda (fvar x)
| not_lambda_ref  : forall x, not_lambda (ref x)
| not_lambda_app  : forall x y, not_lambda (app x y)
| not_lambda_new  : forall x y z, not_lambda (new x y z)
| not_lambda_sel  : forall x y, not_lambda (sel x y).
Hint Constructors not_lambda.

(* the hard case is T = tp_rfn TP DS -- need to appeal to a more powerful lemma that says that expansion is monotone under subtyping *)  
Lemma lambdas_dont_have_members: forall E t T q1 DS q2,  E |= t ~: T @ q1 -> E |= T ~< DS @ q2 -> DS <> nil -> not_lambda t.
Proof. 
  introv HT HX HNotNil. generalize dependent q1. generalize dependent t. 
  induction HX; intros; 
    try (inverts HT; eapply (IHHX _ _ _ (typing_sub _ H)); eauto); 
    try tauto. 
  
  destruct t; auto.

*)

(* false: does not work when e.l -> e'.l -- the IH says e' may still be a lambda 
Lemma path_red_path_or_lambda: forall s t t' s', path t -> s |~ t ~~> t' ~| s' -> path t' \/ (exists T, exists tb, t' = lam T tb).
Proof.
  intros. induction H0; inverts H; eauto. inverts H2; auto. right; eauto. set (IHred H2) as IH. left.
*)

(*
Lemma invert_typing_sel : forall E S t U q, E |= sel t l ~: T @ q -> exists q0, exists q1, exists T, E |= lam S t ~: (tp_fun S T) @ q0 /\ sub_tp E q1 (tp_fun S T) U.
Admitted.
*)

(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "../metalib") ***
*** End: ***
*)  