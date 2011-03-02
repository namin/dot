Set Implicit Arguments.
Require Import List.
Require Import syntax_binding theory.
Require Import Metatheory LibTactics_sf support.
Require Import Coq.Program.Equality.

Lemma and_decls_nil : forall ds1 ds2, and_decls ds1 ds2 nil -> ds1 = nil /\ ds2 = nil.
Proof. introv. intros. 
  unfold and_decls in H. destruct H as [_ [HDSOk1 [HDSOk2 H]]]. assert (forall (l : label) (d : decl), (
      (exists d1 d2, LabelMapImpl.binds l d1 ds1 /\ LabelMapImpl.binds l d2 ds2 /\ and_decl d1 d2 d) \/
       LabelMapImpl.binds l d ds1 \/ 
       LabelMapImpl.binds l d ds2) -> LabelMapImpl.binds l d nil). unfold iff in H. apply H.  clear H.  
        unfold LabelMapImpl.binds in H0. simpl in H0. induction ds1; induction ds2; auto; destruct a. 
         destruct (H0 l d). right. right. simpl. left. auto.
         destruct (H0 l d). right. left. simpl. left. auto.
         destruct (H0 l d). right. left. simpl. left. auto.
Qed.

Lemma and_decls_nil_2 : forall ds, and_decls nil nil ds -> ds = nil.
Proof. introv. intros.   unfold and_decls in H. destruct H as [_ [HDSOk1 [HDSOk2 H]]]. unfold iff in H. assert (forall (l : label) (d : decl),
      LabelMapImpl.binds l d ds ->
      (exists d1 d2,
       LabelMapImpl.binds l d1 nil /\
       LabelMapImpl.binds l d2 nil /\ and_decl d1 d2 d) \/
      LabelMapImpl.binds l d nil \/ LabelMapImpl.binds l d nil) by apply H. clear H.
   induction ds; auto. destruct a. unfold LabelMapImpl.binds in H0. destruct (H0 l d); simpl; auto.
   destruct H. destruct H. destruct H. destruct H. 
   destruct H. destruct H. destruct H. 
Qed.

Lemma or_decls_nil_2 : forall ds1 ds2 ds, or_decls ds1 ds2 ds -> ds1 = nil \/ ds2 = nil -> ds = nil.
Proof. Admitted.
  
Inductive subsumes_top : tp -> Prop := 
 | et_tst_op : subsumes_top tp_top
 | st_rfn : forall T, subsumes_top T -> subsumes_top (tp_rfn T nil)
 | st_and : forall T1 T2, subsumes_top T1 -> subsumes_top T2 -> subsumes_top (tp_and T1 T2)
 | st_or1 : forall T1 T2, subsumes_top T1 -> subsumes_top (tp_or T1 T2)
 | st_or2 : forall T1 T2, subsumes_top T2 -> subsumes_top (tp_or T1 T2).

Hint Constructors subsumes_top has_tp_sel.


Lemma opening_pres_subsumes_top : forall T p p', subsumes_top (T ^tp^ p) -> subsumes_top (T ^tp^ p'). 
Proof.
  intros. unfold open_tp in *; simpl. induction T; try solve [inverts H; simpl; auto].
    simpl in *. inverts H.
    induction l. simpl. auto. inverts H2.
Qed.

Section InvSubTop.
  Let P0_ (E: env) (q: quality) (t: tm) (T: tp) (H: E  |=  t ~: T  @ q) := True.
  Let P1_ (E : env) (q : quality) (T : tp) (DS : decls) (H: E |= T ~< DS @ q) := subsumes_top T -> DS = nil.
  Let P2_ (E : env) (q : quality) (T T' : tp) (H: E |= T ~<: T' @ q) := subsumes_top T -> ~ has_tp_sel T' -> subsumes_top T'.
  Let P3_ (e : env) (q : quality) (d d0 : decl) (H: sub_decl e q d d0) := True.
  Let P4_ (e : env) (t t0 : tm) (H: path_eq e t t0) := True.
  Let P5_ (e : env) (H: wf_env e) := True.
  Let P6_ (c : ctx) (H: wf_ctx c) := True.
  Let P7_ (c : ctx) (p : pex) (H: wf_pex c p) := True.
  Let P8_ (e : env) (t : tp) (H: wf_tp e t) := True.
  Let P9_ (e : env) (d : decl) (H: wf_decl e d) := True.

Lemma invert_subtyping_top : 
   (forall E q T DS, E |= T ~< DS @ q -> subsumes_top T -> DS = nil) /\
   (forall E q T T', E |= T ~<: T' @ q -> subsumes_top T -> ~ has_tp_sel T' -> subsumes_top T').
Proof. 
  mutind_typing P0_ P1_ P2_ P3_ P4_ P5_ P6_ P7_ P8_ P9_; intros; try solve [inverts H;eauto | inverts H0;eauto | inverts H1;eauto | eauto ].

(*cases: *)
    (* expands_rfn *) inverts H0. assert (DSP = nil) by auto. subst. apply and_decls_nil_2; assumption.
    (* expands_and *) inverts H1. assert (DS1 = nil) by auto; assert (DS2 = nil) by auto. subst. apply and_decls_nil_2; assumption.
    (* expands_or *) assert (DS1 = nil \/ DS2 = nil) by (inverts H1; [left; auto | right; auto]). apply or_decls_nil_2 with (ds1 := DS1) (ds2 := DS2); assumption.
    (* sub_tp_rfn_intro *) assert (DS = nil) by auto. subst. inverts H0; auto. 
    (* sub_tp_rfn *) assert (DS2 = nil). inverts H. unfold LabelSetImpl.Subset in s. simpl in s. induction DS2; auto. destruct a. assert (LabelSetImpl.In l LabelSetImpl.empty). apply (s l). eapply (LabelMapImpl.binds_In); eauto. LabelSetDecide.fsetdec. subst. inverts H. auto.
    (* sub_tp_rfn_precise *) inverts H0; auto.
      assert (DS2 = nil). unfold LabelSetImpl.Subset in e. simpl in e. induction DS2; auto. destruct a. simpl in e. unfold LabelSetImpl.Equal in e. unfold iff in e. destruct (e l) as [HF _]. assert ( LabelSetImpl.In l LabelSetImpl.empty). LabelSetDecide.fsetdec. rewrite (LabelSetFacts.empty_iff) in H0. contradiction H0. subst. auto.
    (* sub_tp_tpsel_lower *) unfold not in H2. contradiction (H2 (hts_tp_sel _ _)).
    (* sub_tp_path_eq *) apply opening_pres_subsumes_top with (p := p'); auto.
    (* sub_tp_and_r*) unfold not in *. assert (has_tp_sel T1 -> False). intros. apply H2. apply hts_and1; auto. assert (has_tp_sel T2 -> False). intros. apply H2. apply hts_and2; auto. apply st_and; [apply H; auto | apply H0; auto].
    (* sub_tp_or_r1 *) apply st_or1; eauto. 
    (* sub_tp_or_r2 *) apply st_or2; eauto.
Qed.
End InvSubTop.


Lemma invert_subtyping_and_l : forall E T1 T2 T q, E |= tp_and T1 T2 ~<: T @ q -> 
  (exists q, E |= T1 ~<: T @ q) /\ (exists q, E |= T2 ~<: T @ q).
Proof. Admitted.


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
  Let P6_ (c : ctx) (H: wf_ctx c) := True.
  Let P7_ (c : ctx) (p : pex) (H: wf_pex c p) := True.
  Let P8_ (e : env) (t : tp) (H: wf_tp e t) := True.
  Let P9_ (e : env) (d : decl) (H: wf_decl e d) := True.

(* this is the first lemma that i tried to prove that relies on E only having x : T for which T has been checked for full well-formedness, as performed by typing_new  *)
Lemma invert_subtyping_fun : 
   (forall E q T DS, E |= T ~< DS @ q -> exists T1, exists T2, subsumes_fun_tp T T1 T2 -> DS = nil) /\
   (forall E q T T', E |= T ~<: T' @ q -> forall T1 T2, subsumes_fun_tp T T1 T2 -> ~ has_tp_sel T' -> exists T1', exists T2', subsumes_fun_tp T' T1' T2' /\ exists q, E |= T1' ~<: T1 @ q /\ exists q, E |= T2 ~<: T2' @ q).
Proof. 
  mutind_typing P0_ P1_ P2_ P3_ P4_ P5_ P6_ P7_ P8_ P9_; intros; try solve [ eauto ].

(*Lemma invert_subtyping_fun: forall E S T U S' T' q1 q2 s,  E |== s ->
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
Admitted.

End InvSubFun.

(* more convenient interface to above *)
Lemma invert_expands_fun: forall E S T DS q,  E |= tp_fun S T ~< DS @ q -> DS = nil.
Proof. Admitted.



Lemma sub_tp_trans_safe : forall E s S TMid T q1 q2, E |== s -> E |= S ~<: TMid @ q1 -> E |= TMid ~<: T @ q2 -> exists q3, E |= S ~<: T @ q3.
Proof. Admitted. (* intros.  set TMid as TMid'. destruct TMid; try solve [exists (q1 & q2); apply sub_tp_trans with (TMid := TMid'); auto; unfold not; intros ? ? HH; inversion HH | idtac]. clear TMid'.   dependent induction H0.*)

Lemma expands_sub_safe : forall E s S TMid DS q1 q2, E |== s -> E |= S ~<: TMid @ q1 -> E |= TMid ~< DS @ q2 -> exists q3, E |= S ~< DS @ q3.
Proof. Admitted.

Lemma invert_typing_lam : forall E S t U q s, E |== s -> E |= lam S t ~: U @ q -> 
      exists q1, exists L, exists T, (forall x, x \notin L -> (ctx_bind E x S) |= (t ^^ x) ~: T @ q1) /\
      wf_tp E (tp_fun S T) /\ lc_tp T /\
      exists q2, sub_tp E q2 (tp_fun S T) U.
Proof. Admitted.

Lemma invert_typing_sel: forall E t l T q s, E |== s -> E |= sel t l ~: T @ q ->   
      exists T', exists q1, E |= t ~: T' @ q1 /\
      exists DS, exists q2, E |= T' ~< DS @ q2 /\
      exists D, LabelMapImpl.binds l D DS /\
      exists S, open_decl_cond D t (decl_tm S) /\
      exists q3, sub_tp E q3 S T.
Proof.
  introv. intros Hstowf H. dependent induction H. 
    repeat eexists; eauto. apply sub_tp_refl.
    destruct (IHtyping t l); auto. exists x. 
    destruct H1 as [q1' [HT [DS [q2' [HX [D [Hin [S0 [HOpen [q3 HSub]]]]]]]]]].
    repeat ((eapply sub_tp_trans_safe; eauto) || (esplit; eauto)).
Qed.





(*
(*Lemma top_insensitive_opening : forall T p, subsumes_top T -> subsumes_top (T ^tp^ p). 
Proof.
  intros. induction H; auto; unfold open_tp in *; simpl; auto.
Qed.*)

(*Instance EqDec_eq_label : EqDec_eq label.
Proof. unfold EqDec_eq. decide equality; decide equality; eauto. Defined.

Set Implicit Arguments.
Lemma binds_map_3 : forall A B (x: label) (b: B) (f: A -> B) E,
  (forall a b, f a = f b -> a = b) ->
  LabelMapImpl.uniq E ->
  LabelMapImpl.binds x b (LabelMapImpl.map f E) ->
  exists a, LabelMapImpl.binds x a E /\ b = f a.
Proof.
  labelmap induction E; intros HFInjection HUniq HBTail.
    inversion HBTail. set (LabelMapImpl.binds_map_1 B A f x b HBTail).
set (LabelMapImpl.binds_app_uniq_1 B x b _ _ HUniq HBTail).
    unfold LabelMapImpl.binds in *. simpl in *. destruct (x == x0); subst.
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