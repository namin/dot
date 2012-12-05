(** The DOT calculus -- Rules *)

Require Export Dot_Labels.
Require Import Metatheory.
Require Export Dot_Syntax Dot_Definitions.

(* ********************************************************************** *)
(** * #<a name="red"></a># Reduction *)
Reserved Notation "s |~ a ~~> b  ~| s'" (at level 60).

(* ********************************************************************** *)
(** * #<a name="ev"></a># Evaluation *)
Reserved Notation "s |~ a ~>~ b ~| s'" (at level 60).

(* ********************************************************************** *)
(** * #<a name="typing"></a># Typing *)
(* Type Assigment *)
Reserved Notation "E |= t ~: T" (at level 69).
(* Membership *)
Reserved Notation "E |= t ~mem~ l ~: D" (at level 69).
(* Expansion *)
Reserved Notation "E |= T ~< DS" (at level 69).
(* Subtyping *)
Reserved Notation "E |= t ~<: T" (at level 69).
(* Declaration subsumption *)
(* E |= D ~<: D' *)
(* Well-formed types *)
(* E |= T ~wf~ *)
(* Well-formed declarations *)
(* E |= D ~wf *)

Inductive red : store -> tm -> store -> tm -> Prop :=
(*| red_beta : forall s T t v,
     wf_store s ->
     lc_tm (lam T t) ->
     value v ->
     s |~ (app (lam T t)) v ~~> (t ^^ v) ~| s*)
(*| red_app_fun : forall s s' t e e',
     lc_tm t ->
     s |~        e ~~> e'        ~| s' ->
     s |~  app e t ~~> app e' t  ~| s'*)
(*| red_app_arg : forall s s' v e e',
     value v ->
     s |~        e ~~> e'        ~| s' ->
     s |~  app v e ~~> app v e'  ~| s'*)
  | red_msel : forall s a Tc ags l t v,
     wf_store s ->
     binds a (Tc, ags) s ->
     lbl.binds l t ags ->
     method_label l ->
     value v ->
     s |~ (msel (fvar a) l v) ~~> (t ^^ v) ~| s
  | red_msel_tgt1 : forall s s' l e1 e2 e1',
     s |~             e1 ~~> e1'             ~| s' ->
     s |~ (msel e1 l e2) ~~> (msel e1' l e2) ~| s'
  | red_msel_tgt2 : forall s s' l v1 e2 e2',
    value v1 ->
     s |~             e2 ~~> e2'             ~| s' ->
     s |~ (msel v1 l e2) ~~> (msel v1 l e2') ~| s'
  | red_sel :forall s a Tc ags l v,
     wf_store s -> 
     binds a (Tc, ags) s ->
     lbl.binds l v ags -> 
     s |~ (sel (fvar a) l) ~~> v ~| s
  | red_sel_tgt : forall s s' l e e',
     s |~         e ~~> e'         ~| s' ->
     s |~ (sel e l) ~~> (sel e' l) ~| s'
  | red_new : forall s Tc a ags t,
     wf_store s -> 
     lc_tm (new Tc ags t) ->
     concrete Tc ->
     (forall l v, lbl.binds l v (ags ^args^ fvar a) -> (value_label l /\ value v) \/ (method_label l)) ->
     a `notin` dom s ->
     s |~   (new Tc ags t) ~~> t ^^ (fvar a)   ~| ((a ~ ((Tc, ags ^args^ (fvar a)))) ++ s)
where "s |~ a ~~> b  ~| s'" := (red s a s' b).

Inductive ev : store -> tm -> store -> tm -> Prop :=
  | ev_value : forall s v,
     wf_store s ->
     value v ->
     s |~ v ~>~ v ~| s
(*| ev_beta : forall si s1 s2 sf t1 t2 t11 v2 vf T,
     si |~ t1 ~>~ (lam T t11) ~| s1 ->
     lc_tm (lam T t11) ->
     s1 |~ t2 ~>~ v2 ~| s2 ->
     s2 |~ (t11 ^^ v2) ~>~ vf ~| sf ->
     si |~ (app t1 t2) ~>~ vf ~| sf*)
  | ev_msel : forall si s1 s2 sf a Tc ags l t tl t' v' v,
     si |~ t ~>~ (fvar a) ~| s1 ->
     s1 |~ t' ~>~ v' ~| s2 ->
     binds a (Tc, ags) sf ->
     lbl.binds l tl ags ->
     s2 |~ (tl ^^ v') ~>~ v ~| sf ->
     method_label l ->
     si |~ (msel t l t') ~>~ v ~| sf
  | ev_sel : forall si sf a Tc ags t l v,
     si |~ t ~>~ (fvar a) ~| sf ->
     binds a (Tc, ags) sf ->
     lbl.binds l v ags ->
     value_label l ->
     si |~ (sel t l) ~>~ v ~| sf
  | ev_new : forall si sf a Tc ags t vf,
     lc_tm (new Tc ags t) ->
     concrete Tc ->
     (forall l v, lbl.binds l v ags -> (value_label l /\ value (v ^^ (fvar a))) \/ (method_label l)) ->
     a `notin` dom si ->
     ((a ~ ((Tc, ags ^args^ (fvar a)))) ++ si) |~ t ~>~ vf ~| sf ->
     si |~ (new Tc ags t) ~>~ vf ~| sf
where "s |~ a ~>~ b  ~| s'" := (ev s a s' b).

Inductive typing : env -> tm -> tp -> Prop :=
  | typing_var : forall E x T,
      wf_env E ->
      lc_tp T ->
      binds x T E ->
      E |= (fvar x) ~: T
(*| typing_ref : forall G P a T args,
      wf_env (G, P) ->
      binds a (T, args) P ->
      (G, P) |= (ref a) ~: T*)
  | typing_sel : forall E t l T',
      value_label l ->
      E |= t ~mem~ l ~: (decl_tm T') ->
      wfe_tp E T' ->
      E |= (sel t l) ~: T'
  | typing_msel : forall E t t' l S T T',
      method_label l ->
      E |= t ~mem~ l ~: (decl_mt S T) ->
      E |= t' ~: T' ->
      E |= T' ~<: S ->
      wfe_tp E T ->
      E |= (msel t l t') ~: T
(* | typing_app : forall E t t' S T T',
      E |= t ~: (tp_fun S T) ->
      E |= t' ~: T' ->
      E |= T' ~<: S ->
      E |= (app t t') ~: T*)
(* | typing_abs : forall L E S t T,
      wfe_tp E S ->
      (forall x, x \notin L -> (ctx_bind E x S) |= (t ^ x) ~: T) ->
      E |= (lam S t) ~: (tp_fun S T)*)
  | typing_new : forall L L' E Tc args t T' ds,
      wfe_tp E Tc ->
      concrete Tc ->
      E |= Tc ~< ds ->
      lbl.uniq args ->
      (forall l v, lbl.binds l v args -> (value_label l \/ method_label l) /\ (exists d, decls_binds l d ds)) ->
      (forall x, x \notin L ->
        (forall l d, decls_binds l d ds ->
          (forall S U, d ^d^ x = decl_tp S U -> (ctx_bind E x Tc) |= S ~<: U) /\
          (forall S U, d ^d^ x = decl_mt S U -> (exists t,
            lbl.binds l t args /\ method_label l /\ (forall y, y \notin L' ->
              wfe_tp E S /\
              (exists U', (ctx_bind (ctx_bind E x Tc) y S) |= ((t ^ x) ^ y) ~: U' /\ (ctx_bind (ctx_bind E x Tc) y S) |= U' ~<: U)))) /\
          (forall V, d ^d^ x = decl_tm V -> (exists v,
            lbl.binds l v args /\ value_label l /\ value (v ^ x) /\ (exists V', (ctx_bind E x Tc) |= (v ^ x) ~: V' /\ (ctx_bind E x Tc) |= V' ~<: V))))) ->
      (forall x, x \notin L -> (ctx_bind E x Tc) |= t ^ x ~: T') ->
      E |= (new Tc args t) ~: T'
where "E |= t ~: T" := (typing E t T)

with mem : env -> tm -> label -> decl -> Prop :=
  | mem_path : forall E p l T DS D,
      path p ->
      E |= p ~: T ->
      expands E T DS ->
      decls_binds l D DS ->
      mem E p l (D ^d^ p)
  | mem_term : forall E t l T DS D,
      E |= t ~: T ->
      expands E T DS ->
      decls_binds l D DS ->
      lc_decl D ->
      mem E t l D
where "E |= t ~mem~ l ~: D" := (mem E t l D)

with expands : env -> tp -> decls -> Prop :=
  | expands_any : forall E T DS,
     expands_iter nil E T DS ->
     expands E T DS
where "E |= T ~< DS" := (expands E T DS)

with expands_iter : list (tp * decls) -> env -> tp -> decls -> Prop :=
  | expands_iter_rfn : forall M E T DSP DS DSM,
      expands_iter M E T DSP ->
      and_decls DSP (decls_fin DS) DSM ->
      expands_iter M E (tp_rfn T DS) DSM
  | expands_iter_tsel_cache : forall M E p L DS,
      path p ->
      type_label L ->
      In ((tp_sel p L), DS) M ->
      decls_ok DS ->
      expands_iter M E (tp_sel p L) DS
  | expands_iter_tsel_fix : forall M E p L S U DS,
      path p ->
      type_label L ->
      ~(In ((tp_sel p L), DS) M) ->
      E |= p ~mem~ L ~: (decl_tp S U) ->
      expands_fix (tp_sel p L) (decls_fin nil) M E U DS ->
      decls_ok DS ->
      expands_iter M E (tp_sel p L) DS
  | expands_iter_and : forall M E T1 DS1 T2 DS2 DSM,
      expands_iter M E T1 DS1 ->
      expands_iter M E T2 DS2 ->
      and_decls DS1 DS2 DSM ->
      expands_iter M E (tp_and T1 T2) DSM
  | expands_iter_or : forall M E T1 DS1 T2 DS2 DSM,
      expands_iter M E T1 DS1 ->
      expands_iter M E T2 DS2 ->
      or_decls DS1 DS2 DSM ->
      expands_iter M E (tp_or T1 T2) DSM
  | expands_iter_top : forall M E,
      wf_env E ->
      expands_iter M E tp_top (decls_fin nil)
(*| expands_fun : forall E S T,
      wf_env E ->
      expands E (tp_fun S T) (decls_fin nil)*)
  | expands_iter_bot : forall M E DS,
      wf_env E ->
      bot_decls DS ->
      expands_iter M E tp_bot DS

with expands_fix : tp -> decls -> list (tp * decls) -> env -> tp -> decls -> Prop :=
  | expands_fix_one : forall Ts M E T DS,
      expands_iter ((Ts ~ DS) ++ M) E T DS ->
      expands_fix Ts DS M E T DS
  | expands_fix_rec : forall Ts DS M E T DSA DSB,
      expands_iter ((Ts ~ DS) ++ M) E T DSA ->
      DS <> DSA ->
      expands_fix Ts DSA M E T DSB ->
      expands_fix Ts DS M E T DSB

with sub_tp : env -> tp -> tp -> Prop :=
  | sub_tp_refl : forall E T,
      wf_env E -> wfe_tp E T ->
      E |= T ~<: T
(*| sub_tp_fun : forall E S1 S2 T1 T2,
      E |= T1 ~<: S1 ->
      E |= S2 ~<: T2 ->
      E |= (tp_fun S1 S2) ~<: (tp_fun T1 T2)*)
  | sub_tp_rfn_r : forall L E S T DS' DS,
      E |= S ~<: T ->
      E |= S ~< DS' ->
      decls_ok (decls_fin DS) ->       
      (forall z, z \notin L -> forall_decls (ctx_bind E z S) (DS' ^ds^ z) ((decls_fin DS) ^ds^ z) sub_decl) ->
      decls_dom_subset (decls_fin DS) DS' ->
      wfe_tp E (tp_rfn T DS) ->
      E |= S ~<: (tp_rfn T DS)
  | sub_tp_rfn_l : forall E T T' DS,
      E |= T ~<: T' ->
      decls_ok (decls_fin DS) ->
      wfe_tp E (tp_rfn T DS) ->
      E |= (tp_rfn T DS) ~<: T'
  | sub_tp_tsel_r : forall E p L S U S',
      path p ->
      type_label L ->
      E |= p ~mem~ L ~: (decl_tp S U) ->
      E |= S ~<: U ->
      E |= S' ~<: S ->
      wfe_tp E (tp_sel p L) ->
      E |= S' ~<: (tp_sel p L)
  | sub_tp_tsel_l : forall E p L S U U',
      path p ->
      type_label L ->
      E |= p ~mem~ L ~: (decl_tp S U) ->
      E |= S ~<: U ->
      E |= U ~<: U' ->
      wfe_tp E (tp_sel p L) ->
      E |= (tp_sel p L) ~<: U'
  | sub_tp_and_r : forall E T T1 T2,
      E |= T ~<: T1 -> E |= T ~<: T2 ->
      E |= T ~<: (tp_and T1 T2)
  | sub_tp_and_l1 : forall E T T1 T2,
      wf_env E -> wfe_tp E T2 ->
      E |= T1 ~<: T ->
      E |= (tp_and T1 T2) ~<: T
  | sub_tp_and_l2 : forall E T T1 T2,
      wf_env E -> wfe_tp E T1 ->
      E |= T2 ~<: T ->
      E |= (tp_and T1 T2) ~<: T
  | sub_tp_or_r1 : forall E T T1 T2,
      wf_env E -> wfe_tp E T2 ->
      E |= T ~<: T1 ->
      E |= T ~<: (tp_or T1 T2)
  | sub_tp_or_r2 : forall E T T1 T2,
      wf_env E -> wfe_tp E T1 ->
      E |= T ~<: T2 ->
      E |= T ~<: (tp_or T1 T2)
  | sub_tp_or_l : forall E T T1 T2,
      E |= T1 ~<: T -> E |= T2 ~<: T ->
      E |= (tp_or T1 T2) ~<: T
  | sub_tp_top : forall E T,
      wf_env E -> wfe_tp E T ->
      E |= T ~<: tp_top
  | sub_tp_bot : forall E T,
      wf_env E -> wfe_tp E T ->
      E |= tp_bot ~<: T
where "E |= S ~<: T" := (sub_tp E S T)

with sub_decl : env -> decl -> decl -> Prop :=
  | sub_decl_tp : forall E S1 T1 S2 T2,
      E |= S2 ~<: S1 ->
      E |= T1 ~<: T2 ->
      sub_decl E (decl_tp S1 T1) (decl_tp S2 T2)
  | sub_decl_tm : forall E T1 T2,
      E |= T1 ~<: T2 ->
      sub_decl E (decl_tm T1) (decl_tm T2)

with wf_tp : env -> tp -> Prop :=
  | wf_rfn : forall L E T DS,
      decls_ok (decls_fin DS) ->
      wf_tp E T ->
      (forall z, z \notin L ->
        forall l d, decls_binds l d (decls_fin DS) -> (wf_decl (ctx_bind E z (tp_rfn T DS)) (d ^d^ z))) ->
      wf_tp E (tp_rfn T DS)
(*| wf_fun : forall E T1 T2,
      wf_tp E T1 ->
      wf_tp E T2 ->
      wf_tp E (tp_fun T1 T2)*)
(*  | wf_tsel_1 : forall E p L S U,
      path p ->
      type_label L ->
      E |= p ~mem~ L ~: (decl_tp S U) ->
      wf_tp E S ->
      wf_tp E U ->
      wf_tp E (tp_sel p L)
  | wf_tsel_2 : forall E p L U,
      path p ->
      type_label L ->
      E |= p ~mem~ L ~: (decl_tp tp_bot U) ->
      wf_tp E (tp_sel p L)*)
  | wf_tsel : forall E p L S U,
      path p ->
      type_label L ->
      E |= p ~mem~ L ~: (decl_tp S U) ->
      wf_tp E (tp_sel p L)
  | wf_and : forall E T1 T2,
      wf_tp E T1 ->
      wf_tp E T2 ->
      wf_tp E (tp_and T1 T2)
  | wf_or : forall E T1 T2,
      wf_tp E T1 ->
      wf_tp E T2 ->
      wf_tp E (tp_or T1 T2)
  | wf_bot : forall E,
      wf_tp E tp_bot
  | wf_top : forall E,
      wf_tp E tp_top

with wf_decl : env -> decl -> Prop :=
  | wf_decl_tp : forall E S U,
      wf_tp E S ->
      wf_tp E U ->
      wf_decl E (decl_tp S U)
  | wf_decl_tm : forall E T,
      wf_tp E T ->
      wf_decl E (decl_tm T)

with wfe_tp : env -> tp -> Prop :=
  | wfe_any : forall E T DT,
      wf_tp E T ->
      E |= T ~< DT ->
      wfe_tp E T
.

(* ********************************************************************** *)
(** * #<a name="auto"></a># Automation *)

Scheme typing_indm         := Induction for typing Sort Prop
  with mem_indm            := Induction for mem Sort Prop
  with expands_indm        := Induction for expands Sort Prop
  with expands_iter_indm   := Induction for expands_iter Sort Prop
  with expands_fix_indm    := Induction for expands_fix Sort Prop
  with sub_tp_indm         := Induction for sub_tp Sort Prop
  with sub_decl_indm       := Induction for sub_decl Sort Prop
  with wf_tp_indm          := Induction for wf_tp Sort Prop
  with wf_decl_indm        := Induction for wf_decl Sort Prop
  with wfe_tp_indm         := Induction for wfe_tp Sort Prop
.

Combined Scheme typing_mutind from typing_indm, mem_indm, expands_indm, expands_iter_indm, expands_fix_indm, sub_tp_indm, sub_decl_indm, wf_tp_indm, wf_decl_indm, wfe_tp_indm.

Require Import LibTactics_sf.
Ltac mutind_typing P1_ P2_ P3_ P4_ P5_ P6_ P7_ P8_ P9_ P10_ :=
  cut ((forall E t T (H: E |= t ~: T), (P1_ E t T H)) /\
  (forall E t l d (H: E |= t ~mem~ l ~: d), (P2_ E t l d H)) /\
  (forall E T DS (H: E |= T ~< DS), (P3_ E T DS H)) /\
  (forall M E T DS (H: expands_iter M E T DS), (P4_ M E T DS H)) /\
  (forall Ts Ds M E T DS (H: expands_fix Ts Ds M E T DS), (P5_ Ts Ds M E T DS H)) /\
  (forall E T T' (H: E |= T ~<: T'), (P6_  E T T' H))  /\
  (forall (e : env) (d d' : decl) (H : sub_decl e d d'), (P7_ e d d' H)) /\
  (forall (e : env) (t : tp) (H : wf_tp e t), (P8_ e t H)) /\
  (forall (e : env) (d : decl) (H : wf_decl e d), (P9_ e d H)) /\
  (forall (e : env) (t : tp) (H : wfe_tp e t), (P10_ e t H))); [tauto |
    apply (typing_mutind P1_ P2_ P3_ P4_ P5_ P6_ P7_ P8_ P9_ P10_); try unfold P1_, P2_, P3_, P4_, P5_, P6_, P7_, P8_, P9_, P10_ in *; try clear P1_ P2_ P3_ P4_ P5_ P6_ P7_ P8_ P9_ P10_; [  (* only try unfolding and clearing in case the PN_ aren't just identifiers *)
      Case "typing_var" | Case "typing_sel" | Case "typing_msel" | Case "typing_new" | Case "mem_path" | Case "mem_term" | Case "expands_any" | Case "expands_iter_rfn" | Case "expands_iter_tsel_cache" | Case "expands_iter_tsel_fix" | Case "expands_iter_and" | Case "expands_iter_or" | Case "expands_iter_top" | Case "expands_iter_bot" | Case "expands_fix_one" | Case "expands_fix_rec" | Case "sub_tp_refl" | Case "sub_tp_rfn_r" | Case "sub_tp_rfn_l" | Case "sub_tp_tsel_r" | Case "sub_tp_tsel_l" | Case "sub_tp_and_r" | Case "sub_tp_and_l1" | Case "sub_tp_and_l2" | Case "sub_tp_or_r1" | Case "sub_tp_or_r2" | Case "sub_tp_or_l" | Case "sub_tp_top" | Case "sub_tp_bot" | Case "sub_decl_tp" | Case "sub_decl_tm" | Case "wf_rfn" | Case "wf_tsel" | Case "wf_and" | Case "wf_or" | Case "wf_bot" | Case "wf_top" | Case "wf_decl_tp" | Case "wf_decl_tm" | Case "wfe_any" ];
      introv; eauto ].

Section TestMutInd.
(* mostly reusable boilerplate for the mutual induction: *)
  Let Ptyp (E: env) (t: tm) (T: tp) (H: E |=  t ~: T) := True.
  Let Pmem (E: env) (t: tm) (l: label) (d: decl) (H: E |= t ~mem~ l ~: d) := True.
  Let Pexp (E: env) (T: tp) (DS : decls) (H: E |= T ~< DS) := True.
  Let Pexi (M: list (tp * decls)) (E: env) (T: tp) (DS : decls) (H: expands_iter M E T DS) := True.
  Let Pexf (Ts: tp) (Ds: decls) (M: list (tp * decls)) (E: env) (T: tp) (DS : decls) (H: expands_fix Ts Ds M E T DS) := True.
  Let Psub (E: env) (T T': tp) (H: E |= T ~<: T') := True.
  Let Psbd (E: env) (d d': decl) (H: sub_decl E d d') := True.
  Let Pwft (E: env) (t: tp) (H: wf_tp E t) := True.
  Let Pwfd (E: env) (d: decl) (H: wf_decl E d) := True.
  Let Pwfe (E: env) (t: tp) (H: wfe_tp E t) := True.
Lemma EnsureMutindTypingTacticIsUpToDate : True.
Proof. mutind_typing Ptyp Pmem Pexp Pexi Pexf Psub Psbd Pwft Pwfd Pwfe; intros; auto. Qed.
End TestMutInd.

(*
*** Local Variables:
*** coq-load-path: ("metalib" "lib")
*** End:
*)
