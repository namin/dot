Set Implicit Arguments.
Require Import List.
Require Import syntax_binding.
Require Import Metatheory support.

Reserved Notation "E |= t ~:% T" (at level 69).
Reserved Notation "E |= t ~<% T" (at level 69).

Inductive typing_mini : env -> tm -> tp -> Prop :=
   | typing_mini_var : forall G P x T bi,
      wf_env_mini (G, P) -> 
      (*env.*)binds x (T, bi) G ->
      (G, P) |= (fvar x) ~:% T

   | typing_mini_sel : forall E t T' D DS l T,
      E |= t ~:% T' -> E |= T' ~<% tp_rfn tp_top DS -> lbl.binds l D DS -> open_decl_cond D t (decl_tm T) ->
      E |= (sel t l) ~:% T

   | typing_mini_new : forall L E Tc args t T ds,
      wf_tp_mini E Tc ->
      concrete Tc ->
      E |= Tc ~<% tp_rfn tp_top ds -> (* TODO: must be precise *)
      lbl.uniq args -> (* ctor args are unique by label *)
      (lbl.dom ds) [=l=] (lbl.dom args) -> (* all ctor args must have declaration with same label*)
      (forall x, x \notin L -> (forall l d, lbl.binds l d ds -> 
(* Each lower bound must be a subtype of the corresponding upper bound. Since there's not transivity in this system, don't need to track the binding as untrusted *)
        (forall U T, d ^d^ x = decl_tp T U -> (ctx_bind E x Tc) |= T ~<% U) /\ 
(* For each term member, there's a ctor argument with the same label that provides a well-typed value *)
        (forall T, d ^d^ x = decl_tm T -> (exists v,  
          lbl.binds l v args /\ value (v ^^ x) /\ (exists T', (ctx_bind E x Tc) |= (v ^^ x) ~:% T' /\ (ctx_bind E x Tc) |= T' ~<% T))))) ->
      (forall x, x \notin L -> (ctx_bind E x Tc) |= (t ^^ x) ~:% T) ->  (* x.L is now a valid middle man in sub_tp_trans since the type members in Tc's expansion have been checked *)
      (* lc_tp T ->  not needed -- implied by typing_mini_regular for the above judgement *)
      E |= (new Tc args t) ~:% T
where "E |= t ~:% T" := (typing_mini E t T)

with wf_env_mini : env -> Prop := 
  | wf_env_mini_nil : forall P, wf_env_mini (nil, P)
  | wf_env_mini_cons : forall G P x T bi,
     wf_env_mini (G, P) ->
     vars_ok_tp (G, P) T ->
     x `notin` dom G -> 
     wf_env_mini ((x ~ (T, bi) ++ G), P)

with sub_tp_mini : env -> tp -> tp -> Prop :=

  | sub_tp_mini_tpsel_r : forall E p T' DS L S U,
      lbl.binds L (decl_tp S U) DS -> 
      E |= p ~:% T' -> E |= T' ~<% (tp_rfn tp_top DS) ->
      path p -> (* no need for path_safe when transitivity is not a rule *)
      E |= (S ^tp^ p) ~<% (tp_sel p L) (* no need for slack, it's in sub_tp_mini_rfn_r already through member subsumption *)

  | sub_tp_mini_rfn_r : forall L E T T' Tpar DSP DS DS1 DS2, (* T' = tp_top and DS1 = DS2 --> recover expands_rfn*)
      E |= T ~<% T' ->
      (forall z, z \notin L -> forall_decls (ctx_bind E z T) (DS1 ^ds^ z) (DS2 ^ds^ z) sub_decl_mini) ->
      and_decls DSP DS DS1 ->
      lbl.dom DS2 [<l=] lbl.dom DS1 -> (* no longer implied by sub_decls, but that forall/exists construction made induction impractical *)
      E |= T ~<% (tp_rfn Tpar DS) -> E |= Tpar ~<% (tp_rfn tp_top DSP) ->  (* was E |= T ~< DS1 *)
      E |= T ~<% (tp_rfn T' DS2) 

  | sub_tp_mini_top  : forall E T, E |= T ~<% tp_top

(* this rule has the same structure as FSub's Sa-Trans-Tvar (p. 422) *)
  | sub_tp_mini_tpsel_l : forall E p T' DS L S U,
      lbl.binds L (decl_tp S U) DS ->
      E |= p ~:% T' -> E |= T' ~<% (tp_rfn tp_top DS) -> 
      path p ->
      E |= (tp_sel p L) ~<% (U ^tp^ p) (* no need for slack, it's in sub_tp_mini_rfn_r already through member subsumption *)

  | sub_tp_mini_rfn_l : forall E T DS T', 
      E |= T ~<% T' -> 
      E |= (tp_rfn T DS) ~<% T'

  | sub_tp_mini_bot  : forall E T, E |= tp_bot ~<% T (* hide bottom down here, where it belongs *)

where "E |= T1 ~<% T2" := (sub_tp_mini E T1 T2)

with sub_decl_mini : env -> decl -> decl -> Prop :=
  | sub_decl_mini_tp : forall E S1 T1 S2 T2,
      E |= S2 ~<% S1 ->
      E |= T1 ~<% T2 ->
      sub_decl_mini E (decl_tp S1 T1) (decl_tp S2 T2)
  | sub_decl_mini_tm : forall E T1 T2,
      E |= T1 ~<% T2 ->
      sub_decl_mini E (decl_tm T1) (decl_tm T2)

with wf_tp_mini : env -> tp -> Prop :=
  | wf_tp_mini_rfn : forall L E T DS,
      decls_ok DS -> (* no dups or invalid label/decl combos *)
      wf_tp_mini E T ->
      (forall z, z `notin` L ->
          forall l d, lbl.binds l d DS -> (wf_decl_mini (ctx_bind E z (tp_rfn T DS)) (d ^d^ z))) ->
      wf_tp_mini E (tp_rfn T DS)
  | wf_tp_mini_tsel : forall E T' DS p L S U,
      path p ->
      E |= p ~:% T' -> E |= T' ~<% tp_rfn tp_top DS -> lbl.binds L (decl_tp S U) DS ->
      wf_tp_mini E (S ^tp^ p) -> 
      wf_tp_mini E (U ^tp^ p) ->
      wf_tp_mini E (tp_sel p L)
  | wf_tp_mini_bot : forall E, wf_tp_mini E tp_bot
  | wf_tp_mini_top : forall E, wf_tp_mini E tp_top

with wf_decl_mini : env -> decl -> Prop :=
  | wf_decl_mini_tp : forall E S U,
     wf_tp_mini E S ->
     wf_tp_mini E U ->
     wf_decl_mini E (decl_tp S U)
  | wf_decl_mini_tm : forall E T,
     wf_tp_mini E T ->
     wf_decl_mini E (decl_tm T).



Scheme typing_mini_indm   := Induction for typing_mini    Sort Prop
  with wf_env_mini_indm   := Induction for wf_env_mini    Sort Prop
  with sub_tp_mini_indm   := Induction for sub_tp_mini    Sort Prop
  with sub_decl_mini_indm := Induction for sub_decl_mini  Sort Prop
  with wf_tp_mini_indm    := Induction for wf_tp_mini     Sort Prop
  with wf_decl_mini_indm  := Induction for wf_decl_mini   Sort Prop.

Combined Scheme typing_mini_mutind from typing_mini_indm, wf_env_mini_indm, sub_tp_mini_indm, sub_decl_mini_indm, wf_tp_mini_indm, wf_decl_mini_indm.


(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "../metalib") ***
*** End: ***
*)  