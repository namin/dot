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
Reserved Notation "E |= T ~< DS" (at level 69).
(* Subtyping *)
Reserved Notation "E |= t ~<: T" (at level 69).
(* Declaration subsumption *)
(* E |= D ~<: D' *)
(* Well-formed types *)
(* E |= T ~wf~ *)
(* Well-formed declarations *)
(* E |= D ~wf *)

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
      E |= Tc ~< ds ->
      lbl.uniq args ->
      (forall l v, lbl.binds l v args -> value_label l /\ (exists d, lbl.binds l d args)) ->
      (forall x, x \notin L ->
        (forall l d, lbl.binds l d ds ->
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
      expands E T DS ->
      lbl.binds l D DS ->
      mem E p l (D ^d^ p)
  | mem_term : forall E t l T DS D,
      E |= t ~: T ->
      expands E T DS ->
      lbl.binds l D DS ->
      lc_decl D ->
      mem E t l D
where "E |= t ~mem~ l ~: D" := (mem E t l D)

with expands : env -> tp -> decls -> Prop :=
  | expands_rfn : forall E T DSP DS DSM,
      expands E T DSP ->
      and_decls DSP DS DSM ->
      expands E (tp_rfn T DS) DSM
  | expands_tsel : forall E p L S U DS,
      path p ->
      type_label L ->
      E |= p ~mem~ L ~: (decl_tp S U) ->
      expands E U DS ->
      expands E (tp_sel p L) DS
  | expands_and : forall E T1 DS1 T2 DS2 DSM,
      expands E T1 DS1 ->
      expands E T2 DS2 ->
      and_decls DS1 DS2 DSM ->
      expands E (tp_and T1 T2) DSM
  | expands_or : forall E T1 DS1 T2 DS2 DSM,
      expands E T1 DS1 ->
      expands E T2 DS2 ->
      or_decls DS1 DS2 DSM ->
      expands E (tp_or T1 T2) DSM
  | expands_top : forall E,
      wf_env E ->
      expands E tp_top nil
  | expands_fun : forall E S T,
      wf_env E ->
      expands E (tp_fun S T) nil
  | expands_bot : forall E DS,
      wf_env E ->
      bot_decls DS ->
      expands E tp_bot DS
where "E |= T ~< DS" := (expands E T DS)

with sub_tp : env -> tp -> tp -> Prop :=
  | sub_tp_refl : forall E T,
      E |= T ~<: T
  | sub_tp_fun : forall E S1 S2 T1 T2,
      E |= T1 ~<: S1 ->
      E |= S2 ~<: T2 ->
      E |= (tp_fun S1 S2) ~<: (tp_fun T1 T2)
  | sub_tp_rfn_r : forall L E S T DS' DS,
      E |= S ~<: T ->
      E |= S ~< DS' ->
      decls_ok DS ->       
      (forall z, z \notin L -> forall_decls (ctx_bind E z S) (DS' ^ds^ z) (DS ^ds^ z) sub_decl) ->
      lbl.dom DS [<l=] lbl.dom DS' ->
      E |= S ~<: (tp_rfn T DS)
  | sub_tp_rfn_l : forall E T T' DS,
      E |= T ~<: T' ->
      decls_ok DS ->
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
      decls_ok DS ->
      wf_tp E T ->
      (forall z, z \notin L ->
        forall l d, lbl.binds l d DS -> (wf_decl (ctx_bind E z (tp_rfn T DS)) (d ^d^ z))) ->
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
