(** The DOT calculus -- Preservation. *)

Set Implicit Arguments.
Require Import List.
Require Export Dot_Labels.
Require Import Metatheory LibTactics_sf.
Require Export Dot_Syntax Dot_Definitions Dot_Rules Dot_Lemmas Dot_Transitivity.
Require Import Coq.Program.Equality.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Logic.Decidable.
(*
Definition typing_store G s :=
  wf_store s
  /\ (forall a Tc argsRT, binds a (Tc, argsRT) s ->
       wfe_tp (G,s) Tc
    /\ exists args, argsRT = args ^args^ (ref a)
    /\ concrete Tc
    /\ lbl.uniq args
    /\ exists ds, (G, s) |= Tc ~< ds
    /\ (forall l v, lbl.binds l v args -> (value_label l \/ method_label l) /\ (exists d, decls_binds l d ds))
    /\ (exists L L', (forall x, x \notin L -> (forall l d, decls_binds l d ds ->
       (type_label l -> (exists S U, d ^d^ x = decl_tp S U /\ (ctx_bind (G,s) x Tc) |= S ~<: U)) /\
       (method_label l -> (exists S U, d ^d^ x = decl_mt S U /\ (exists v, lbl.binds l v args /\ (forall y, y \notin L' -> (exists U', (ctx_bind (ctx_bind (G,s) x Tc) y S) |= ((v ^ x) ^ y) ~: U' /\ (ctx_bind (ctx_bind (G,s) x Tc) y S) |= U' ~<: U))))) /\
       (value_label l -> (exists V, d ^d^ x = decl_tm V /\ (exists v, lbl.binds l v args /\ syn_value(v ^ x) /\ (exists V', (ctx_bind (G,s) x Tc) |= (v ^ x) ~: V' /\ (ctx_bind (G,s) x Tc) |= V' ~<: V)))))))).

Notation "G |== s" := (typing_store G s) (at level 68).

Definition ok_env G_s :=
  wf_env G_s /\ (forall x T, binds x T (fst G_s) -> wfe_tp G_s T).

Notation "G_s |= 'ok'" := (ok_env G_s) (at level 69).

Lemma env_weakening_notin_wfe_tp: forall L E S T x t,
  x `notin` L -> ctx_bind E x S |= t ^ x ~: T -> wfe_tp (ctx_bind E x S) T ->
  wfe_tp E T.
Proof. (* TODO *) Admitted.

Lemma env_weakening_notin_sub_tp: forall L E S T T' x,
  x `notin` L -> ctx_bind E x S |= T ~<: T' ->
  E |= T ~<: T'.
Proof. (* TODO *) Admitted.

Lemma ok_env_plus: forall E s x S,
  (E,s) |= ok -> E |== s -> 
  ((x, S) :: E, s) |= ok.
Proof. (* TODO *) Admitted.

Lemma typing_store_plus: forall E s x S,
  (E,s) |= ok -> E |== s ->
  ((x, S) :: E) |== s.
Proof. (* TODO *) Admitted.

Lemma wf_env_gamma_uniq : forall E G P,
  wf_env E -> E = (G,P) -> uniq G.
Proof.
  introv Hwf Heq. gen G.
  induction Hwf. introv Heq. inversion Heq. subst. auto.
  introv Heq. inversion Heq. subst. auto.
Qed.

Lemma wf_store_uniq : forall P,
  wf_store P -> uniq P.
Proof.
  introv Hwf.
  induction Hwf. auto. auto.
Qed.

Lemma wf_env_store_uniq : forall E G P,
  wf_env E -> E = (G,P) -> uniq P.
Proof.
  introv Hwf Heq. gen P.
  inversion Hwf; introv Heq; inversion Heq; subst; apply wf_store_uniq; assumption.
Qed.

Scheme tp_mem_typing_indm := Induction for typing Sort Prop
  with tp_mem_mem_indm    := Induction for mem Sort Prop
.

Combined Scheme tp_mem_mutind from tp_mem_typing_indm, tp_mem_mem_indm.

Ltac mutind_tp_mem Ptyp Pmem :=
  cut ((forall E t T (H: E |= t ~: T), (Ptyp E t T H)) /\
    (forall E t l d (H: E |= t ~mem~ l ~: d), (Pmem E t l d H))); [try tauto; Case "IH" |
      apply (tp_mem_mutind Ptyp Pmem); try unfold Ptyp, Pmem in *; try clear Ptyp Pmem; [Case "typing_var" | Case "typing_ref" | Case "typing_sel" | Case "typing_msel" | Case "typing_new" | Case "mem_path" | Case "mem_term"]; introv; eauto ].

Lemma expansion_unique : forall E T DS DS',
  E |= T ~< DS -> E |= T ~< DS' -> DS = DS'.
Proof. (* TODO *) Admitted.

Lemma tp_unique : forall E t T T',
  E |= t ~: T -> E |= t ~: T' -> T = T'.
Proof.
  mutind_tp_mem (fun E t T (H: E |= t ~: T) => forall T', E |= t ~: T' -> T = T')
                (fun E t l d (H: E |= t ~mem~ l ~: d) => forall d', E |= t ~mem~ l ~: d' -> d = d').
  Case "IH".
    introv H. inversion H as [H1 H2]. introv HT HT'.
    eauto.
  Case "typing_var".
    introv Hwf Hlc Hbinds. introv HT'. inversion HT'. subst.
    assert (uniq G). apply wf_env_gamma_uniq with (E:=(G,P)) (P:=P). assumption. reflexivity.
    apply binds_unique with (x:=x) (E:=G); assumption.
  Case "typing_ref".
    introv Hwf Hbinds. introv HT'. inversion HT'. subst.
    assert (uniq P). apply wf_env_store_uniq with (E:=(G,P)) (G:=G). assumption. reflexivity.
    assert ((T, args) = (T', args0)) as Heq. apply binds_unique with (x:=a) (E:=P); assumption.
    inversion Heq. subst. reflexivity.
  Case "typing_sel".
    introv Hlv Hmem IHmem Hwfe. intros T''. introv Hsel. inversion Hsel. subst.
    assert (decl_tm T' = decl_tm T'') as Heq. apply IHmem. assumption.
    inversion Heq. subst. reflexivity.
  Case "typing_msel".
    introv Hlm Hmem IHmem Ht'T' IHtyp Hsame Hwfe. intros T''. introv Hmsel. inversion Hmsel. subst.
    assert (decl_mt S T = decl_mt S0 T'') as Heq. apply IHmem. assumption.
    inversion Heq. subst. reflexivity.
  Case "typing_new".
    intros. inversion H0. subst.
    pick fresh x for (union L L0). eauto.
  Case "mem_path".
    (* rely on uniqueness of expansion *) skip.
  Case "mem_term".
    (* rely on uniqueness of expansion *) skip.
Qed.

Lemma mem_unique : forall E t l d d',
  E |= t ~mem~ l ~: d -> E |= t ~mem~ l ~: d' -> d = d'.
Proof. (* TODO *) Admitted.

Lemma tp_regular : forall E s t T,
  (E,s) |= ok -> E |== s ->
  (E,s) |= t ~: T ->
  wfe_tp (E,s) T.
Proof.
  introv Hok Hes H. dependent induction H.
  Case "var".
    inversion Hok as [Hwf_env Hbinds].
    apply (Hbinds x T). simpl. assumption.
  Case "ref".
    inversion Hes as [Hwf_store Hcond].
    apply (proj1 (Hcond a T args H0)).
  Case "sel".
    assumption.
  Case "msel".
    assumption.
  Case "new".
    pick fresh x.
    assert (wfe_tp (ctx_bind (E,s) x Tc) T') as Hwfe_tp.
      apply H6 with (x:=x). apply notin_union_1 in Fr. assumption.
      simpl. apply ok_env_plus; assumption.
      simpl. apply typing_store_plus; assumption.
      simpl. reflexivity.
    apply env_weakening_notin_wfe_tp with (L:=L) (S:=Tc) (x:=x) (t:=t).
    apply notin_union_1 in Fr. assumption. 
    apply H5. apply notin_union_1 in Fr. assumption.
    assumption.
Qed.

Lemma preserved_env_nil_ok : forall s t s' t',
  (nil,s) |= ok ->
  s |~ t ~~> t' ~| s' ->
  (nil,s') |= ok.
Proof.
  introv Hok Hr. induction Hr; try solve [assumption | apply IHHr; assumption].
  Case "red_new".
  inversion H0. subst. inversion Hok as [Henv Hbinds].
  split.
  apply wf_env_nil. apply wf_store_cons_tp; assumption.
  introv Hbinds_nil. inversion Hbinds_nil.
Qed.

Lemma preserved_env_nil_typing : forall s t s' t' T,
  nil |== s ->
  s |~ t ~~> t' ~| s' ->
  (nil,s) |= t ~: T ->
  nil |== s'.
Proof.
  introv Hc Hr. gen T. dependent induction Hr; introv Ht.
  Case "red_msel".
    assumption.
  Case "red_msel_tgt1".
    inversion Ht. inversion H3; subst; apply IHHr with (T:=T1); assumption.
  Case "red_msel_tgt2".
    inversion Ht. apply IHHr with (T:=T'); assumption.
  Case "red_sel".
    assumption.
  Case "red_sel_tgt".
    inversion Ht. inversion H3; subst; apply IHHr with (T:=T0); assumption.
  Case "red_new".
    (* TODO *) skip.
Qed.

Lemma preserved_env_ok : forall G s t s' t',
  (G,s) |= ok ->
  s |~ t ~~> t' ~| s' ->
  (G,s') |= ok.
Proof. (* TODO *) Admitted.

Lemma preserved_env_typing : forall G s t s' t' T,
  G |== s ->
  s |~ t ~~> t' ~| s' ->
  (G,s) |= t ~: T ->
  G |== s'.
Proof. (* TODO *) Admitted.

Lemma preserved_wfe : forall G s t  s' t' T,
  (G,s) |= ok ->
  G |== s ->
  s |~ t ~~> t' ~| s' ->
  wfe_tp (G,s) T ->
  wfe_tp (G,s') T.
Proof. (* TODO *) Admitted.

Lemma preserved_subtype : forall G s t s' t' S T,
  (G,s) |= ok ->
  G |== s ->
  s |~ t ~~> t' ~| s' ->
  (G,s) |= S ~<: T ->
  (G,s') |= S ~<: T.
Proof. (* TODO *) Admitted.

Lemma preserved_tp : forall G s t s' t' tt T,
  (G,s) |= ok ->
  G |== s ->
  s |~ t ~~> t' ~| s' ->
  (G,s) |= tt ~: T ->
  (G,s') |= tt ~: T.
Proof. (* TODO *) Admitted.

Lemma preserved_mem : forall G s t s' t' e l d,
  (G,s) |= ok ->
  G |== s ->
  s |~ t ~~> t' ~| s' ->
  (G,s) |= e ~mem~ l ~: d ->
  (G,s') |= e ~mem~ l ~: d.
Proof. (* TODO *) Admitted.

Lemma tp_two_ways : forall L x G s Tc a args t T,
  (G,s) |= ok -> G |== s ->
  binds a (Tc, args) s ->
  x `notin` L ->
  ctx_bind (G, s) x Tc |= t ^ x ~: T ->
  (G, s) |= t ^^ ref a ~: T.
Proof. (* TODO *) Admitted.

Lemma decl_two_ways : forall L x G s Tc a args d d',
  (G,s) |= ok -> G |== s ->
  binds a (Tc, args) s ->
  x `notin` L ->
  d ^d^ x = d' ->
  d ^d^ ref a = d'.
Proof. (* TODO *) Admitted.

Lemma subst_noop_if_lc : forall T v,
  lc_tp T -> decl_tm T ^d^ v = decl_tm T.
Proof. (* TODO *) Admitted.

Lemma tp_env_extended_two_ways : forall L G s Tc t T a args,
  (G,s) |= ok -> G |== s ->
  (G,[(a, (Tc,  args))] ++ s) |= ok -> G |== [(a, (Tc, args))] ++ s ->
  (forall x, x `notin` L -> ctx_bind (G, s) x Tc |= t ^ x ~: T) ->
  (G, [(a, (Tc, args))] ++ s) |= t ^^ ref a ~: T.
Proof.
  introv Hok Hc Hok' Hc' Ht.
  pick fresh x.
  assert (x `notin` L) as FrL. auto.
  specialize (Ht x FrL). dependent induction t.
  Case "n".
    unfold open in Ht. simpl in Ht. unfold "^^". simpl. destruct (equiv_dec 0 n).
    SCase "n = 0".
      inversion Ht. subst.
      assert (uniq ((x, Tc)::G)). apply wf_env_gamma_uniq with (E:=((x, Tc)::G,s)) (P:=s). assumption. reflexivity.
      assert (T = Tc) as Heq. apply binds_mid_eq with (x:=x) (F:=nil) (E:=G); auto.
      subst.
      inversion Hok' as [Henv' Hbinds'].
      eapply typing_ref. auto. auto.
    SCase "n <> 0".
      inversion Ht.
  Case "a".
    unfold open in Ht. simpl in Ht. unfold open. simpl.
    inversion Ht. subst.
    assert (x `notin` fv_tm a0) as Fra0. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption.
    assert (a0 <> x) as Hneq. simpl in Fra0. apply notin_singleton_1. assumption.
    inversion Hok' as [Henv' Hbinds'].
    apply typing_var; try assumption. rewrite_env (nil ++ G). eapply binds_remove_mid. rewrite_env (nil ++ [(x,Tc)] ++ G) in H5. apply H5. assumption.
  Case "ref".
    inversion Hok' as [Henv' Hbinds'].
    inversion Ht. subst. unfold open. simpl. eapply typing_ref. assumption.
    assert (forall aargs, binds l (T, args0) ((a, aargs) :: s)) as Hbindsa. intros. rewrite_env (nil ++ [(a, aargs)] ++ s). apply binds_weaken. simpl. assumption.
    apply Hbindsa.
  Case "new".
    skip.
  Case "sel".
    skip.
  Case "msel".
    skip.
Qed.

Lemma binds_exists_before_open : forall l v args a,
  lbl.binds l v (args ^args^ ref a) ->
  exists v', lbl.binds l v' args /\ v' ^^ ref a = v.
Proof. (* TODO *) Admitted.

Lemma nil_to_ctx_mem : forall G s t l d,
  (G,s) |= ok -> G |== s -> (nil,s) |= t ~mem~ l ~: d ->
  (G,s) |= t ~mem~ l ~: d.
Proof. (* TODO *) Admitted.

Lemma sub_tp_decl_tm : forall L x E S T DS DT l dS dT vT S' T',
  x `notin` L ->
  E |= S ~<: T ->
  E |= S ~< DS ->
  E |= T ~< DT ->
  decls_binds l dS DS ->
  decls_binds l dT DT ->
  E |= vT ~: T ->
  dT ^d^ vT = decl_tm T' ->
  dS ^d^ x = decl_tm S' ->
  ctx_bind E x S |= S' ~<: T'.
Proof. (* TODO *) Admitted.

(*

Lemma preserved_same_tp : forall G s t s' t' T T',
  (G,s) |= ok ->
  G |== s ->
  s |~ t ~~> t' ~| s' ->
  (G,s) |= T' ~=: T ->
  (G,s') |= T' ~=: T.
Proof.
  introv Hok Hc Hr Hs. inversion Hs. subst.
  apply same_tp_any; apply preserved_subtype with (s:=s) (t:=t) (t':=t'); assumption.
Qed.

Lemma membership_value_same_tp : forall E t1 T1 t1' T1' l T,
  E |= t1 ~: T1 ->
  E |= t1' ~: T1' ->
  E |= T1' ~=: T1 ->
  E |= t1 ~mem~ l ~: decl_tm T ->
  exists T', E |= t1' ~mem~ l ~: decl_tm T' /\ E |= T' ~=: T.
Proof. (* TODO *) Admitted.

Lemma membership_method_same_tp : forall E t1 T1 t1' T1' l S T,
  E |= t1 ~: T1 ->
  E |= t1' ~: T1' ->
  E |= T1' ~=: T1 ->
  E |= t1 ~mem~ l ~: decl_mt S T ->
  exists S' T', E |= t1' ~mem~ l ~: decl_mt S' T' /\ E |= S ~=: S' /\ E |= T' ~=: T.
Proof. (* TODO *) Admitted.

Lemma same_tp_transitive : forall TMid E T T',
  E |= T ~=: TMid -> E |= TMid ~=: T' -> E |= T ~=: T'.
Proof.
  introv HT HT'. inversion HT. inversion HT'. subst.
  apply same_tp_any; apply sub_tp_transitive with (TMid:=TMid); assumption.
Qed.

Lemma same_tp_reflexive : forall E T T',
  E |= T ~=: T' -> E |= T' ~=: T.
Proof.
  introv H. inversion H. subst. apply same_tp_any; assumption.
Qed.

Lemma value_to_ref_sub_tp : forall E v a Tv Ta,
  E |= v ~: Tv -> E |= ref a ~: Ta ->
  E |= Ta ~<: Tv.
Proof. (* TODO *) Admitted.

Definition preservation := forall G s t T s' t',
  (G,s) |= ok ->
  G |== s ->
  (G,s) |= t ~: T ->
  s |~ t ~~> t' ~| s' ->
  exists T',
  (G,s') |= t' ~: T' /\
  (G,s') |= T' ~=: T.

Theorem preservation_holds : preservation.
Proof. unfold preservation.
  introv Hok Hc Ht Hr.
  assert ((G,s') |= ok) as Hok'. apply preserved_env_ok with (s:=s) (t:=t) (t':=t'); assumption.
  assert (G |== s') as Hc'. apply preserved_env_typing with (s:=s) (t:=t) (t':=t') (T:=T); assumption.
  gen T. induction Hr.
  Case "red_msel".  (* TODO *) skip.
  Case "red_msel_tgt1".
    introv Ht. inversion Ht. subst.
    inversion H3. subst.
    specialize (IHHr Hok Hc Hok' Hc' T0 H1). inversion IHHr as [Th' IHHr']. inversion IHHr' as [Ht' Hs'].
    assert (exists S' T', (G,s') |= e1' ~mem~ l ~: decl_mt S' T' /\ (G,s') |= S ~=: S' /\ (G,s') |= T' ~=: T) as Hmem'.
      apply membership_method_same_tp with (t1:=e1) (T1:=T0) (T1':=Th'); try assumption.
      apply preserved_tp with (s:=s) (t:=e1) (t':=e1'); assumption.
      apply preserved_mem with (s:=s) (t:=e1) (t':=e1'); assumption.
    inversion Hmem' as [S'' Hmem'']. inversion Hmem'' as [T'' Hmem''']. inversion Hmem''' as [Hmem_ Hsame_]. inversion Hsame_ as [HsameS HsameT].
    exists T''. split.
    apply typing_msel with (S:=S'') (T':=T'); try assumption.
      apply preserved_tp with (s:=s) (t:=e1) (t':=e1'); assumption.
      apply same_tp_transitive with (TMid:=S); try assumption.
      apply preserved_same_tp with (s:=s) (t:=e1) (t':=e1'); assumption.
      inversion HsameT. subst. auto. assumption.
    subst.
    specialize (IHHr Hok Hc Hok' Hc' T0 H). inversion IHHr as [Th' IHHr']. inversion IHHr' as [Ht' Hs'].
    assert (exists S' T', (G,s') |= e1' ~mem~ l ~: decl_mt S' T' /\ (G,s') |= S ~=: S' /\ (G,s') |= T' ~=: T) as Hmem'.
      apply membership_method_same_tp with (t1:=e1) (T1:=T0) (T1':=Th'); try assumption.
      apply preserved_tp with (s:=s) (t:=e1) (t':=e1'); assumption.
      apply preserved_mem with (s:=s) (t:=e1) (t':=e1'); assumption.
    inversion Hmem' as [S'' Hmem'']. inversion Hmem'' as [T'' Hmem''']. inversion Hmem''' as [Hmem_ Hsame_]. inversion Hsame_ as [HsameS HsameT].
    exists T''. split.
    apply typing_msel with (S:=S'') (T':=T'); try assumption.
      apply preserved_tp with (s:=s) (t:=e1) (t':=e1'); assumption.
      apply same_tp_transitive with (TMid:=S); try assumption.
      apply preserved_same_tp with (s:=s) (t:=e1) (t':=e1'); assumption.
      inversion HsameT. subst. auto. assumption.
  Case "red_msel_tgt2".
    introv Ht. inversion Ht. subst.
    inversion Hok' as [Henv' Hbinds'].
    specialize (IHHr Hok Hc Hok' Hc' T' H6). inversion IHHr as [Th' IHHr']. inversion IHHr' as [Ht' Hs'].
    exists T. split.
      apply typing_msel with (S:=S) (T':=Th'); try assumption.
      apply preserved_mem with (s:=s) (t:=e2) (t':=e2'); assumption.
      apply same_tp_transitive with (TMid:=T'); try assumption.
      apply preserved_same_tp with (s:=s) (t:=e2) (t':=e2'); assumption.
      apply preserved_wfe with (s:=s) (t:=e2) (t':=e2'); assumption.
      apply same_tp_any; apply sub_tp_refl; try assumption; apply preserved_wfe with (s:=s) (t:=e2) (t':=e2'); assumption.
  Case "red_sel".
    introv Ht. inversion Ht. subst.
    inversion Hok as [Henv Hbinds].
    inversions Hc.
    specialize (H7 a Tc ags H0).
    inversions H7.
    inversions H11. rename x into args.
    inversions H7.
    inversions H13.
    inversions H11.
    inversions H14. rename x into ds.
    inversions H11.
    inversions H15.
    inversions H16. rename x into L.
    inversions H15. rename x into L'.
    inversion H5.
    SCase "no upcast".
      subst.
      inversion H4. subst.
      inversion H10.
      SSCase "mem path".
      subst.
      assert (T0 = Tc) as Heq. apply tp_unique with (E:=(G,s)) (t:=ref a). assumption. eapply typing_ref. assumption. apply H0.
      subst.
      pick fresh x.
      assert (x `notin` L) as FrL. auto.
      assert (ds = DS) as Heq. apply expansion_unique with (E:=(G,s)) (T:=Tc); assumption.
      subst.
      specialize (H16 x FrL l D H24).
      inversions H16.
      inversions H22.
      remember H15 as Hlabel. clear HeqHlabel.
      apply H23 in H15.
      inversion H15 as [V HV].
      inversion HV as [Hdecl HV'].
      inversion HV' as [va HV''].
      inversion HV'' as [Hbinds_va HV'''].
      inversion HV''' as [Hvalue_va HV''''].
      inversion HV'''' as [V' HV'_].
      inversion HV'_ as [HV'1 HV'2].
      assert (lbl.binds l (va ^^ ref a) (args ^args^ ref a)) as Hbinds_va'. unfold "^^". unfold "^args^". apply lbl.binds_map_2. assumption.
      assert (va ^^ ref a = v'') as Heq. eapply lbl.binds_unique. apply Hbinds_va'. assumption. apply lbl.uniq_map_2. assumption.
      assert ((G,s) |= va ^^ ref a ~: V') as Htv''. eapply tp_two_ways with (L:=L); try assumption. apply H0. apply FrL. assumption.
      rewrite Heq in Htv''.
      exists V'. split. assumption.
      assert (D ^d^ ref a = decl_tm V) as Hdecl'. eapply decl_two_ways with (L:=L). apply Hok. assumption. apply H0. apply FrL. assumption.
      rewrite H17 in Hdecl'. inversion Hdecl'. subst. eapply env_weakening_notin_same_tp with (L:=L). apply FrL. apply HV'2.
      SSCase "mem term".
      subst.
      assert (T0 = Tc) as Heq. apply tp_unique with (E:=(G,s)) (t:=ref a). assumption. eapply typing_ref. assumption. apply H0.
      subst.
      pick fresh x.
      assert (x `notin` L) as FrL. auto.
      assert (ds = DS) as Heq. apply expansion_unique with (E:=(G,s)) (T:=Tc); assumption.
      subst.
      specialize (H16 x FrL l (decl_tm T) H19).
      inversions H16.
      inversions H22.
      remember H15 as Hlabel. clear HeqHlabel.
      apply H23 in H15.
      inversion H15 as [V HV].
      inversion HV as [Hdecl HV'].
      inversion HV' as [va HV''].
      inversion HV'' as [Hbinds_va HV'''].
      inversion HV''' as [Hvalue_va HV''''].
      inversion HV'''' as [V' HV'_].
      inversion HV'_ as [HV'1 HV'2].
      assert (lbl.binds l (va ^^ ref a) (args ^args^ ref a)) as Hbinds_va'. unfold "^^". unfold "^args^". apply lbl.binds_map_2. assumption.
      assert (va ^^ ref a = v'') as Heq. eapply lbl.binds_unique. apply Hbinds_va'. assumption. apply lbl.uniq_map_2. assumption.
      assert ((G,s) |= va ^^ ref a ~: V') as Htv''. eapply tp_two_ways with (L:=L); try assumption. apply H0. apply FrL. assumption.
      rewrite Heq in Htv''.
      exists V'. split. assumption.
      assert ((decl_tm T) ^d^ ref a = decl_tm V) as Hdecl'. eapply decl_two_ways with (L:=L). apply Hok. assumption. apply H0. apply FrL. assumption.
      inversion H20. subst.
      assert (decl_tm T ^d^ ref a = decl_tm T) as Hlc. apply subst_noop_if_lc. assumption.
      rewrite Hlc in Hdecl'. inversion Hdecl'. subst. eapply env_weakening_notin_same_tp with (L:=L). apply FrL. apply HV'2.
    SCase "upcast".
      subst.
      inversion H10.
      SSCase "mem path".
      subst.
      inversion H21. subst.
      remember H1 as Hbinds_v'. clear HeqHbinds_v'.
      apply binds_exists_before_open in H1. inversion H1 as [v'_ H1'].
      inversion H1' as [Hbinds_v'_ Heqv'_].
      specialize (H11 l v'_ Hbinds_v'_).
      inversions H11.
      inversion H24 as [d Hdecls_binds].
      pick fresh x.
      assert (x `notin` L) as FrL. auto.
      specialize (H16 x FrL l d Hdecls_binds).
      inversion H16 as [Htype_label Hlabels].
      inversion Hlabels as [Hmethod_label Hvalue_label].
      specialize (Hvalue_label H2).
      inversion Hvalue_label as [V HV].
      inversion HV as [Hdecl HV'].
      inversion HV' as [va HV''].
      inversion HV'' as [Hbinds_va HV'''].
      inversion HV''' as [Hvalue_va HV''''].
      inversion HV'''' as [V' HV'_].
      inversion HV'_ as [HV'1 HV'2].
      assert (va = v'_) as Heq. eapply lbl.binds_unique. apply Hbinds_va. assumption. assumption.
      subst.
      assert ((G,s) |= v'_ ^^ ref a ~: V') as Htv'_. eapply tp_two_ways with (L:=L); try assumption. apply H0. apply FrL. assumption.
      assert (decl_tm T = decl_tm T') as Heq. eapply mem_unique. apply H10. apply nil_to_ctx_mem; assumption.
      inversion Heq. subst.
      exists T'. split.
      apply typing_wid with (T':=V'). assumption.
      assert ((G,s) |= Tc ~<: T1) as Hsub. apply value_to_ref_sub_tp with (v:=wid v0 T1) (a:=a); try assumption. eapply typing_ref; try assumption. apply H0.
      assert (ctx_bind (G,s) x Tc |= V ~<: T') as Hsubd. eapply sub_tp_decl_tm with (L:=L) (T:=T1) (DS:=ds) (DT:=DS) (l:=l); try assumption. apply Hdecls_binds. apply H26. apply H21. assumption. assumption.
      apply env_weakening_notin_sub_tp with (L:=L) (S:=Tc) (x:=x); try assumption. apply sub_tp_transitive with (TMid:=V). inversion HV'2. assumption. assumption.
      apply same_tp_any; apply sub_tp_refl; try assumption; apply preserved_wfe with (s:=s) (t:=e2) (t':=e2'); assumption.
      SSCase "mem term".
      subst.
      inversion H19. subst.
      remember H1 as Hbinds_v'. clear HeqHbinds_v'.
      apply binds_exists_before_open in H1. inversion H1 as [v'_ H1'].
      inversion H1' as [Hbinds_v'_ Heqv'_].
      specialize (H11 l v'_ Hbinds_v'_).
      inversions H11.
      inversion H24 as [d Hdecls_binds].
      pick fresh x.
      assert (x `notin` L) as FrL. auto.
      specialize (H16 x FrL l d Hdecls_binds).
      inversion H16 as [Htype_label Hlabels].
      inversion Hlabels as [Hmethod_label Hvalue_label].
      specialize (Hvalue_label H2).
      inversion Hvalue_label as [V HV].
      inversion HV as [Hdecl HV'].
      inversion HV' as [va HV''].
      inversion HV'' as [Hbinds_va HV'''].
      inversion HV''' as [Hvalue_va HV''''].
      inversion HV'''' as [V' HV'_].
      inversion HV'_ as [HV'1 HV'2].
      assert (va = v'_) as Heq. eapply lbl.binds_unique. apply Hbinds_va. assumption. assumption.
      subst.
      assert ((G,s) |= v'_ ^^ ref a ~: V') as Htv'_. eapply tp_two_ways with (L:=L); try assumption. apply H0. apply FrL. assumption.
      assert (decl_tm T = decl_tm T') as Heq. eapply mem_unique. apply H10. apply nil_to_ctx_mem; assumption.
      inversion Heq. subst.
      exists T'. split.
      apply typing_wid with (T':=V'). assumption.
      assert ((G,s) |= Tc ~<: T1) as Hsub. apply value_to_ref_sub_tp with (v:=wid v0 T1) (a:=a); try assumption. eapply typing_ref; try assumption. apply H0.
      assert (ctx_bind (G,s) x Tc |= V ~<: T') as Hsubd. eapply sub_tp_decl_tm with (L:=L) (T:=T1) (DS:=ds) (DT:=DS) (l:=l); try assumption. apply Hdecls_binds. apply H21. apply H19. apply subst_noop_if_lc. inversion H22. subst. assumption. assumption.
      apply env_weakening_notin_sub_tp with (L:=L) (S:=Tc) (x:=x); try assumption. apply sub_tp_transitive with (TMid:=V). inversion HV'2. assumption. assumption.
      apply same_tp_any; apply sub_tp_refl; try assumption; apply preserved_wfe with (s:=s) (t:=e2) (t':=e2'); assumption.
  Case "red_sel_tgt".
    introv Ht. inversion Ht. subst.
    inversion H3. subst.
    specialize (IHHr Hok Hc Hok' Hc' T0 H2). inversion IHHr as [Th' IHHr']. inversion IHHr' as [Ht' Hs'].
    assert (exists T', (G,s') |= e' ~mem~ l ~: decl_tm T' /\ (G,s') |= T' ~=: T) as Hmem'.
      apply membership_value_same_tp with (t1:=e) (T1:=T0) (T1':=Th'); try assumption.
      apply preserved_tp with (s:=s) (t:=e) (t':=e'); assumption.
      apply preserved_mem with (s:=s) (t:=e) (t':=e'); assumption.
    inversion Hmem' as [T' Hmem'']. inversion Hmem'' as [Hmem''' HT'eqT].
    exists T'. split.
    apply typing_sel; try assumption.
      inversion HT'eqT. subst. auto.
    assumption.
    subst.
    specialize (IHHr Hok Hc Hok' Hc' T0 H). inversion IHHr as [Th' IHHr']. inversion IHHr' as [Ht' Hs'].
    assert (exists T', (G,s') |= e' ~mem~ l ~: decl_tm T' /\ (G,s') |= T' ~=: T) as Hmem'.
      apply membership_value_same_tp with (t1:=e) (T1:=T0) (T1':=Th'); try assumption.
      apply preserved_tp with (s:=s) (t:=e) (t':=e'); assumption.
      apply preserved_mem with (s:=s) (t:=e) (t':=e'); assumption.
    inversion Hmem' as [T' Hmem'']. inversion Hmem'' as [Hmem''' HT'eqT].
    exists T'. split.
    apply typing_sel; try assumption.
      inversion HT'eqT. subst. auto.
    assumption.
  Case "red_wid_tgt".
    introv Ht. inversion Ht. subst.
    inversion Hok' as [Henv' Hbinds'].
    specialize (IHHr Hok Hc Hok' Hc' T' H2). inversion IHHr as [Th' IHHr']. inversion IHHr' as [Ht' Hs']. inversion Hs' as [Hs1 Hs2]. subst.
    exists T. splits.
    apply typing_wid with (T':=Th'). assumption.
    apply sub_tp_transitive with (TMid:=T').
    assumption. apply preserved_subtype with (s:=s) (t:=e) (t':=e'); assumption.
    apply same_tp_any.
      apply sub_tp_refl. assumption. apply preserved_wfe with (s:=s) (t:=e) (t':=e'); auto.
      apply sub_tp_refl. assumption. apply preserved_wfe with (s:=s) (t:=e) (t':=e'); auto.
  Case "red_new".
    inversion Hok' as [Henv' Hbinds'].
    assert (s |~ new Tc ags t ~~> t ^^ ref a ~| ([(a, (Tc, ags ^args^ ref a))] ++ s)) as Hr. apply red_new; assumption.
    introv Ht. inversion Ht. subst.
    exists T. split.
    apply tp_env_extended_two_ways with (L:=L); assumption.
    pick fresh x.
    assert (x `notin` L) as FrL. auto.
    specialize (H15 x FrL).
    assert (wfe_tp (G,s) T) as Hwfe. apply tp_regular with (t:=new Tc ags t); assumption.
    apply same_tp_any; apply sub_tp_refl; try assumption; apply preserved_wfe with (s:=s) (t:=new Tc ags t) (t':=t ^^ ref a); assumption.
Qed.

*)
*)