(** The DOT calculus -- Rules *)

Require Export Dot_Labels.
Require Import Metatheory.
Require Export Dot_Syntax Dot_Definitions.

(* ********************************************************************** *)
(** * #<a name="red"></a># Reduction *)

Reserved Notation "s |~ a ~~> b  ~| s'" (at level 60).

Inductive red : store -> tm -> store -> tm -> Prop :=
  | red_beta : forall s T t v,
     wf_store s ->
     lc_tm (lam T t) ->
     value v ->
     s |~ (app (lam T t)) v ~~> (t ^^ v) ~| s
  | red_app_fun : forall s s' t e e',
     lc_tm t ->
     s |~        e ~~> e'        ~| s' ->
     s |~  app e t ~~> app e' t  ~| s'
  | red_app_arg : forall s s' v e e',
     value v ->
     s |~        e ~~> e'        ~| s' ->
     s |~  app v e ~~> app v e'  ~| s'

  | red_sel : forall s a Tc ags l v,
     wf_store s -> 
     binds a (Tc, ags) s ->
     lbl.binds l v ags -> 
     s |~ (sel (ref a) l) ~~> v ~| s
  | red_sel_tgt : forall s s' l e e',
     s |~         e ~~> e'         ~| s' ->
     s |~ (sel e l) ~~> (sel e' l) ~| s'
  | red_new : forall s Tc a ags t,
     wf_store s -> 
     lc_tm (new Tc ags t) ->
     concrete Tc ->
     (forall l v, lbl.binds l v ags -> value_label l /\ value (v ^^ (ref a))) ->
     a `notin` dom s ->
     s |~   (new Tc ags t) ~~> t ^^ (ref a)   ~| ((a ~ ((Tc, ags ^args^ (ref a)))) ++ s)

where "s |~ a ~~> b  ~| s'" := (red s a s' b).

(* ********************************************************************** *)
(** * #<a name="typing"></a># Typing *)

(* Type Assigment *)
Reserved Notation "E |= t ~: T" (at level 69).
(* Membership *)
Reserved Notation "E |= t ~mem~ l ~: D" (at level 69).
(* Expansion *)
Reserved Notation "E |= T ~< DS @ q" (at level 69).
(* Subtyping *)
Reserved Notation "E |= t ~<: T" (at level 69).
(* Declaration subsumption *)
(* E |= D ~<: D' *)
(* Well-formed types *)
(* E |= T ~wf~ *)
(* Well-formed declarations *)
(* E |= D ~wf *)

Inductive expansion_quality : Set :=
  | complete : expansion_quality
  | loose    : expansion_quality
.

Definition qconj (q1: expansion_quality) (q2: expansion_quality) : expansion_quality :=
  match (q1, q2) with
  | (complete, complete) => complete
  | _ => loose
  end.
Notation "q1 & q2" := (qconj q1 q2) (at level 67).

Inductive typing : env -> tm -> tp -> Prop :=
  | typing_var : forall G P x T,
      wf_env (G, P) ->
      lc_tp T ->
      binds x T G ->
      (G, P) |= (fvar x) ~: T
  | typing_ref : forall G P a T args,
      wf_env (G, P) ->
      binds a (T, args) P ->
      (G, P) |= (ref a) ~: T
  | typing_sel : forall E t l T',
      value_label l ->
      E |= t ~mem~ l ~: (decl_tm T') ->
      E |= (sel t l) ~: T'
  | typing_app : forall E t t' S T T',
      E |= t ~: (tp_fun S T) ->
      E |= t' ~: T' ->
      E |= T' ~<: S ->
      E |= (app t t') ~: T
  | typing_abs : forall L E S t T,
      wf_tp E S ->
      (forall x, x \notin L -> (ctx_bind E x S) |= (t ^ x) ~: T) ->
      E |= (lam S t) ~: (tp_fun S T)
  | typing_new : forall L E Tc args t T' ds,
      wf_tp E Tc ->
      concrete Tc ->
      E |= Tc ~< ds @ complete ->
      lbl.uniq args ->
      (forall l v, lbl.binds l v args -> value_label l /\ (exists d, decls_binds l d ds)) ->
      (forall x, x \notin L ->
        (forall l d, decls_binds l d ds ->
          (forall S U, d ^d^ x = decl_tp S U -> (ctx_bind E x Tc) |= S ~<: U) /\
          (forall V, d ^d^ x = decl_tm V -> (exists v,
            lbl.binds l v args /\ value (v ^ x) /\ (exists V', (ctx_bind E x Tc) |= (v ^ x) ~: V' /\ (ctx_bind E x Tc) |= V' ~<: V))))) ->
      (forall x, x \notin L -> (ctx_bind E x Tc) |= t ^ x ~: T') ->
      E |= (new Tc args t) ~: T'
where "E |= t ~: T" := (typing E t T)

with mem : env -> tm -> label -> decl -> Prop :=
  | mem_path : forall E p l T DS D,
      path p ->
      E |= p ~: T ->
      E |= T ~< DS @ complete ->
      decls_binds l D DS ->
      mem E p l (D ^d^ p)
  | mem_term : forall E t l T DS D,
      E |= t ~: T ->
      E |= T ~< DS @ complete ->
      decls_binds l D DS ->
      lc_decl D ->
      mem E t l D
where "E |= t ~mem~ l ~: D" := (mem E t l D)

with expands : list tp -> env -> tp -> decls -> expansion_quality -> Prop :=
  | expands_loose : forall O E T,
      In T O ->
      expands O E T (decls_fin nil) loose
  | expands_rfn : forall O q E T DSP DS DSM,
      expands ((tp_rfn T DS)::O) E T DSP q ->
      and_decls DSP (decls_fin DS) DSM ->
      expands O E (tp_rfn T DS) DSM q
  | expands_tsel : forall O q E p L S U DS,
      path p ->
      type_label L ->
      E |= p ~mem~ L ~: (decl_tp S U) ->
      expands ((tp_sel p L)::O) E U DS q ->
      expands O E (tp_sel p L) DS q
  | expands_and : forall O q1 q2 E T1 DS1 T2 DS2 DSM,
      expands ((tp_and T1 T2)::O) E T1 DS1 q1 ->
      expands ((tp_and T1 T2)::O) E T2 DS2 q2 ->
      and_decls DS1 DS2 DSM ->
      expands O E (tp_and T1 T2) DSM (q1&q2)
  | expands_or : forall O q1 q2 E T1 DS1 T2 DS2 DSM,
      expands ((tp_or T1 T2)::O) E T1 DS1 q1 ->
      expands ((tp_or T1 T2)::O) E T2 DS2 q2 ->
      or_decls DS1 DS2 DSM ->
      expands O E (tp_or T1 T2) DSM (q1&q2)
  | expands_top : forall O E,
      wf_env E ->
      expands O E tp_top (decls_fin nil) complete
  | expands_fun : forall O E S T,
      wf_env E ->
      expands O E (tp_fun S T) (decls_fin nil) complete
  | expands_bot : forall O E DS,
      wf_env E ->
      bot_decls DS ->
      expands O E tp_bot DS complete
where "E |= T ~< DS @ q" := (expands (nil : list tp) E T DS q)

with sub_tp : env -> tp -> tp -> Prop :=
  | sub_tp_refl : forall E T,
      E |= T ~<: T
  | sub_tp_fun : forall E S1 S2 T1 T2,
      E |= T1 ~<: S1 ->
      E |= S2 ~<: T2 ->
      E |= (tp_fun S1 S2) ~<: (tp_fun T1 T2)
  | sub_tp_rfn_r : forall q L E S T DS' DS,
      E |= S ~<: T ->
      E |= S ~< DS' @ q ->
      decls_ok (decls_fin DS) ->       
      (forall z, z \notin L -> forall_decls (ctx_bind E z S) (DS' ^ds^ z) ((decls_fin DS) ^ds^ z) sub_decl) ->
      decls_dom_subset (decls_fin DS) DS' ->      
      E |= S ~<: (tp_rfn T DS)
  | sub_tp_rfn_l : forall E T T' DS,
      E |= T ~<: T' ->
      decls_ok (decls_fin DS) ->
      E |= (tp_rfn T DS) ~<: T'
  | sub_tp_tsel_r : forall E p L S U S',
      path p ->
      type_label L ->
      E |= p ~mem~ L ~: (decl_tp S U) ->
      E |= S ~<: U ->
      E |= S' ~<: S ->
      E |= S' ~<: (tp_sel p L)
  | sub_tp_tsel_l : forall E p L S U U',
      path p ->
      type_label L ->
      E |= p ~mem~ L ~: (decl_tp S U) ->
      E |= S ~<: U ->
      E |= U ~<: U' ->
      E |= (tp_sel p L) ~<: U'
  | sub_tp_and_r : forall E T T1 T2,
      E |= T ~<: T1 -> E |= T ~<: T2 ->
      E |= T ~<: (tp_and T1 T2)
  | sub_tp_and_l1 : forall E T T1 T2,
      E |= T1 ~<: T ->
      E |= (tp_and T1 T2) ~<: T
  | sub_tp_and_l2 : forall E T T1 T2,
      E |= T2 ~<: T ->
      E |= (tp_and T1 T2) ~<: T
  | sub_tp_or_r1 : forall E T T1 T2,
      E |= T ~<: T1 ->
      E |= T ~<: (tp_or T1 T2)
  | sub_tp_or_r2 : forall E T T1 T2,
      E |= T ~<: T2 ->
      E |= T ~<: (tp_or T1 T2)
  | sub_tp_or_l : forall E T T1 T2,
      E |= T1 ~<: T -> E |= T2 ~<: T ->
      E |= (tp_or T1 T2) ~<: T
  | sub_tp_top : forall E T,
      E |= T ~<: tp_top
  | sub_tp_bot : forall E T,
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
  | wf_fun : forall E T1 T2,
      wf_tp E T1 ->
      wf_tp E T2 ->
      wf_tp E (tp_fun T1 T2)
  | wf_tsel_1 : forall E p L S U,
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
.

(* ********************************************************************** *)
(** * #<a name="auto"></a># Automation *)

Scheme typing_indm         := Induction for typing Sort Prop
  with mem_indm            := Induction for mem Sort Prop
  with expands_indm        := Induction for expands Sort Prop
  with sub_tp_indm         := Induction for sub_tp Sort Prop
  with sub_decl_indm       := Induction for sub_decl Sort Prop
  with wf_tp_indm          := Induction for wf_tp Sort Prop
  with wf_decl_indm        := Induction for wf_decl Sort Prop.

Combined Scheme typing_mutind from typing_indm, mem_indm, expands_indm, sub_tp_indm, sub_decl_indm, wf_tp_indm, wf_decl_indm.

Require Import LibTactics_sf.
Ltac mutind_typing P0_ P1_ P2_ P3_ P4_ P5_ P6_ :=
  cut ((forall E t T (H: E |= t ~: T), (P0_ E t T H)) /\ 
  (forall E t l d (H: E |= t ~mem~ l ~: d), (P1_ E t l d H)) /\
  (forall O E T DS q (H: expands O E T DS q), (P2_ O E T DS q H)) /\ 
  (forall E T T' (H: E |= T ~<: T'), (P3_  E T T' H))  /\ 
  (forall (e : env) (d d' : decl) (H : sub_decl e d d'), (P4_ e d d' H)) /\  
  (forall (e : env) (t : tp) (H : wf_tp e t), (P5_ e t H)) /\  
  (forall (e : env) (d : decl) (H : wf_decl e d), (P6_ e d H))); [tauto | 
    apply (typing_mutind P0_ P1_ P2_ P3_ P4_ P5_ P6_); try unfold P0_, P1_, P2_, P3_, P4_, P5_, P6_ in *; try clear P0_ P1_ P2_ P3_ P4_ P5_ P6_; [  (* only try unfolding and clearing in case the PN_ aren't just identifiers *)
      Case "typing_var" | Case "typing_ref" | Case "typing_sel" | Case "typing_app" | Case "typing_abs" | Case "typing_new" | Case "mem_path" | Case "mem_term" | Case "expands_loose" |Case "expands_rfn" | Case "expands_tsel" | Case "expands_and" | Case "expands_or" | Case "expands_top" | Case "expands_fun" | Case "expands_bot" | Case "sub_tp_refl" | Case "sub_tp_fun" | Case "sub_tp_rfn_r" | Case "sub_tp_rfn_l" | Case "sub_tp_tsel_r" | Case "sub_tp_tsel_l" | Case "sub_tp_and_r" | Case "sub_tp_and_l1" | Case "sub_tp_and_l2" | Case "sub_tp_or_r1" | Case "sub_tp_or_r2" | Case "sub_tp_or_l" | Case "sub_tp_top" | Case "sub_tp_bot" | Case "sub_decl_tp" | Case "sub_decl_tm" | Case "wf_rfn" | Case "wf_fun" | Case "wf_tsel_1" | Case "wf_tsel_2" | Case "wf_and" | Case "wf_or" | Case "wf_bot" | Case "wf_top" | Case "wf_decl_tp" | Case "wf_decl_tm" ]; 
      introv; eauto ].


Section TestMutInd.
(* mostly reusable boilerplate for the mutual induction: *)
  Let Ptyp (E: env) (t: tm) (T: tp) (H: E |=  t ~: T) := True.  
  Let Pmem (E: env) (t: tm) (l: label) (d: decl) (H: E |= t ~mem~ l ~: d) := True.
  Let Pexp (O: list tp) (E: env) (T: tp) (DS : decls) (q : expansion_quality) (H: expands O E T DS q) := True.
  Let Psub (E: env) (T T': tp) (H: E |= T ~<: T') := True.
  Let Psbd (E: env) (d d': decl) (H: sub_decl E d d') := True.
  Let Pwft (E: env) (t: tp) (H: wf_tp E t) := True.
  Let Pwfd (E: env) (d: decl) (H: wf_decl E d) := True.
Lemma EnsureMutindTypingTacticIsUpToDate : True. 
Proof. mutind_typing Ptyp Pmem Pexp Psub Psbd Pwft Pwfd; intros; auto. Qed.
End TestMutInd.
