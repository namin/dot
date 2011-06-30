Set Implicit Arguments.
Require Import List.
Require Import syntax_binding.
Require Import Metatheory support.

Reserved Notation "E |= t ~:! T" (at level 69).
Reserved Notation "E |= t ~<! T" (at level 69).

(* for use in inversion: algorithmic version of type system, omitting quality for now
  (anticipating we'll incorporate it into the types as soon as I can figure out 
   how to syntactically restrict types to quality-canonical ones)*)

(*
subtyping from a parallel universe where transitivity is unheard of; also, to simplify the proof, expansion and sub_decl are rolled into subtyping,
and quality is glossed over (need to improve my Ltac-f to bring it back: existentials must be crushed, qualities normalised), 
since inversion doesn't need to preserve quality this is not urgent, though
(inversion is why we have sub_tp_notrans in the first place -- you try inverting something with an explicit rule for transivity some time)

the order of the rules, and especially the order of the hypotheses in sub_tp_notrans_rfn_r is tuned for eauto 
as used in the proof of transitivity, sub_tp_notrans_trans (more constraining hypotheses come first) 
*)
Inductive typing_alg : env -> tm -> tp -> Prop :=
   | typing_alg_var : forall G P x T bi,
      wf_env_alg (G, P) -> lc_tp T -> (* for typing_alg_regular *)
      (*env.*)binds x (T, bi) G ->
      (G, P) |= (fvar x) ~:! T
   | typing_alg_ref : forall G P a T args, (* only typing_alg and path_eq_alg peek into the store *)
      wf_env_alg (G, P) -> lc_tp T -> (* for typing_alg_regular *)
      binds a (T, args) P ->
      (G, P) |= (ref a) ~:! T
   | typing_alg_sel : forall E t T' D DS l T,
      E |= t ~:! T' -> E |= T' ~<! tp_rfn tp_top DS -> lbl.binds l D DS -> open_decl_cond D t (decl_tm T) ->
      E |= (sel t l) ~:! T

  | typing_alg_peq : forall E t T p p',
      E |= t ~:! (T ^tp^ p) ->
      path_eq_alg E p' p -> (*lc_tm p' ->*)
      E |= t ~:! (T ^tp^ p')

   | typing_alg_app : forall E tf Ta Ta' Tr ta,
      E |= tf ~:! (tp_fun Ta Tr) ->
      E |= ta ~:! Ta' ->
      E |= Ta' ~<! Ta ->
      E |= (app tf ta) ~:! Tr

   | typing_alg_lam : forall L E S t T,
      (forall x, x \notin L -> (ctx_bind_subsumed E x S) |= (t ^^ x) ~:! T) -> 
      wf_tp_alg E (tp_fun S T) ->      (* lc_tp T  not necessary: implied by typing_alg_regular *)
      E |= (lam S t) ~:! (tp_fun S T)

   | typing_alg_new : forall L E Tc args t T ds,
      wf_tp_alg E Tc ->
      concrete Tc ->
      E |= Tc ~<! tp_rfn tp_top ds -> (* TODO: must be precise *)
      lbl.uniq args -> (* ctor args are unique by label *)
      (lbl.dom ds) [=l=] (lbl.dom args) -> (* all ctor args must have declaration with same label*)
      (forall x, x \notin L -> (forall l d, lbl.binds l d ds -> 
(* Each lower bound must be a subtype of the corresponding upper bound. Since there's not transivity in this system, don't need to track the binding as untrusted *)
        (forall U T, d ^d^ x = decl_tp T U -> (ctx_bind E x Tc) |= T ~<! U) /\ 
(* For each term member, there's a ctor argument with the same label that provides a well-typed value *)
        (forall T, d ^d^ x = decl_tm T -> (exists v,  
          lbl.binds l v args /\ value (v ^^ x) /\ (exists T', (ctx_bind E x Tc) |= (v ^^ x) ~:! T' /\ (ctx_bind E x Tc) |= T' ~<! T))))) ->
      (forall x, x \notin L -> (ctx_bind E x Tc) |= (t ^^ x) ~:! T) ->  (* x.L is now a valid middle man in sub_tp_trans since the type members in Tc's expansion have been checked *)
      (* lc_tp T ->  not needed -- implied by typing_alg_regular for the above judgement *)
      E |= (new Tc args t) ~:! T
where "E |= t ~:! T" := (typing_alg E t T)

(* path equality is needed for preservation because evaluation changes types that cannot be related otherwise *)
with path_eq_alg : env -> tm -> tm -> Prop :=
   | peq_refl : forall E p, (* TODO: only needed if proof of preservation depends on it *)
      path p ->
      wf_env_alg E -> path_eq_alg E p p
   | peq_symm : forall E p1 p2, (* used in invert_subtyping_alg_fun *)
      path_eq_alg E p1 p2 ->
      path_eq_alg E p2 p1
   | peq_env : forall G P a Tc args l a',
      wf_env_alg (G, P) ->
      binds a (Tc, args) P ->
      lbl.binds l (ref a') args ->
      path_eq_alg (G, P) (ref a') (sel a l)

   | peq_sel : forall E p p' l T,
      path_eq_alg E p p' ->
      E |= (sel p l) ~:! T ->
      path_eq_alg E (sel p l) (sel p' l)

with wf_env_alg : env -> Prop := 
  | wf_env_alg_nil : forall P, wf_env_alg (nil, P)
  | wf_env_alg_cons : forall G P x T bi,
     wf_env_alg (G, P) ->
     vars_ok_tp (G, P) T ->
     x `notin` dom G -> 
     wf_env_alg ((x ~ (T, bi) ++ G), P)

with sub_tp_alg : env -> tp -> tp -> Prop :=
  | sub_tp_alg_fun : forall E S1 T1 S2 T2,
      E |= S2 ~<! S1 ->
      E |= T1 ~<! T2 -> 
      E |= (tp_fun S1 T1) ~<! (tp_fun S2 T2)

  | sub_tp_alg_tpsel_r : forall E p T' DS L S U,
      lbl.binds L (decl_tp S U) DS -> 
      E |= p ~:! T' -> E |= T' ~<! (tp_rfn tp_top DS) ->
      path_safe E p ->
      E |= (S ^tp^ p) ~<! (tp_sel p L) (* no need for slack, it's in sub_tp_alg_rfn_r already through member subsumption *)

  | sub_tp_alg_rfn_r : forall L E T T' Tpar DSP DS DS1 DS2, (* T' = tp_top and DS1 = DS2 --> recover expands_rfn*)
      E |= T ~<! T' ->
      (forall z, z \notin L -> forall_decls (ctx_bind E z T) (DS1 ^ds^ z) (DS2 ^ds^ z) sub_decl_alg) ->
      and_decls DSP DS DS1 ->
      lbl.dom DS2 [<l=] lbl.dom DS1 -> (* no longer implied by sub_decls, but that forall/exists construction made induction impractical *)
      E |= T ~<! (tp_rfn Tpar DS) -> E |= Tpar ~<! (tp_rfn tp_top DSP) ->  (* was E |= T ~< DS1 *)
      E |= T ~<! (tp_rfn T' DS2) 

  | sub_tp_alg_and_r : forall E T T1 T2,
      E |= T ~<! T1 -> E |= T ~<! T2 ->
      E |= T ~<! (tp_and T1 T2)

  | expands_and : forall E T T1 DS1 T2 DS2 DSM,
      E |= T ~<! (tp_and T1 T2) ->
      E |= T1 ~<! (tp_rfn tp_top DS1) -> E |= T2 ~<! (tp_rfn tp_top DS2) -> and_decls DS1 DS2 DSM ->
      E |= T ~<! (tp_rfn tp_top DSM)

  | sub_tp_alg_or_r1 : forall E T T1 T2,
      E |= T ~<! T1 -> 
      E |= T ~<! (tp_or T1 T2)
  | sub_tp_alg_or_r2 : forall E T T1 T2,
      E |= T ~<! T2 -> 
      E |= T ~<! (tp_or T1 T2)

  | expands_or : forall E T T1 DS1 T2 DS2 DSM,
      E |= T ~<! (tp_or T1 T2) ->
      E |= T1 ~<! (tp_rfn tp_top DS1) -> E |= T2 ~<! (tp_rfn tp_top DS2) -> or_decls DS1 DS2 DSM ->
      E |= T ~<! (tp_rfn tp_top DSM)

  | sub_tp_alg_refl : forall E T, E |= T ~<! T
  | sub_tp_alg_top  : forall E T, E |= T ~<! tp_top
  | expands_top : forall E T, E |= T ~<! (tp_rfn tp_top nil)  (* see e.g, rework_sub_decls' use of sub_tp_alg_rfn_r*)

(* this rule has the same structure as FSub's Sa-Trans-Tvar (p. 422) *)
  | sub_tp_alg_tpsel_l : forall E p T' DS L S U,
      lbl.binds L (decl_tp S U) DS ->
      E |= p ~:! T' -> E |= T' ~<! (tp_rfn tp_top DS) -> 
      path p ->
      E |= (tp_sel p L) ~<! (U ^tp^ p) (* no need for slack, it's in sub_tp_alg_rfn_r already through member subsumption *)

  | sub_tp_alg_rfn_l : forall E T DS T', 
      E |= T ~<! T' -> 
      E |= (tp_rfn T DS) ~<! T'

  | sub_tp_alg_and_l1 : forall E T T1 T2,
      E |= T1 ~<! T -> 
      E |= (tp_and T1 T2) ~<! T
  | sub_tp_alg_and_l2 : forall E T T1 T2,
      E |= T2 ~<! T -> 
      E |= (tp_and T1 T2) ~<! T  

  | sub_tp_alg_or_l : forall E T T1 T2,
      E |= T1 ~<! T -> E |= T2 ~<! T ->
      E |= (tp_or T1 T2) ~<! T

  | sub_tp_alg_bot  : forall E T, E |= tp_bot ~<! T (* hide bottom down here, where it belongs *)

where "E |= T1 ~<! T2" := (sub_tp_alg E T1 T2)

with sub_decl_alg : env -> decl -> decl -> Prop :=
  | sub_decl_alg_tp : forall E S1 T1 S2 T2,
      E |= S2 ~<! S1 ->
      E |= T1 ~<! T2 ->
      sub_decl_alg E (decl_tp S1 T1) (decl_tp S2 T2)
  | sub_decl_alg_tm : forall E T1 T2,
      E |= T1 ~<! T2 ->
      sub_decl_alg E (decl_tm T1) (decl_tm T2)

with wf_tp_alg : env -> tp -> Prop :=
  | wf_rfn : forall L E T DS,
      decls_ok DS -> (* no dups or invalid label/decl combos *)
      wf_tp_alg E T ->
      (forall z, z `notin` L ->
          forall l d, lbl.binds l d DS -> (wf_decl_alg (ctx_bind E z (tp_rfn T DS)) (d ^d^ z))) ->
      wf_tp_alg E (tp_rfn T DS)
  | wf_lam : forall E T1 T2,
      wf_tp_alg E T1 -> 
      wf_tp_alg E T2 ->
      wf_tp_alg E (tp_fun T1 T2)
  | wf_tsel : forall E T' DS p L S U,
      path p ->
(*      E |= p ~mem~ (decl_tp L S U) -> *)
      E |= p ~:! T' -> E |= T' ~<! tp_rfn tp_top DS -> lbl.binds L (decl_tp S U) DS ->
      wf_tp_alg E (S ^tp^ p) -> 
      wf_tp_alg E (U ^tp^ p) ->
      wf_tp_alg E (tp_sel p L)
  | wf_tsel_cls : forall E T' DS p L U,
      path p ->
(*      E |= p ~mem~ (decl_tp L tp_bot U) -> *)
      E |= p ~:! T' -> E |= T' ~<! tp_rfn tp_top DS -> lbl.binds L (decl_tp tp_bot U) DS ->
      wf_tp_alg E (tp_sel p L)
  | wf_and : forall E T1 T2,
      wf_tp_alg E T1 -> 
      wf_tp_alg E T2 ->
      wf_tp_alg E (tp_and T1 T2)
  | wf_or : forall E T1 T2,
      wf_tp_alg E T1 -> 
      wf_tp_alg E T2 ->
      wf_tp_alg E (tp_or T1 T2)
  | wf_bot : forall E, wf_tp_alg E tp_bot
  | wf_top : forall E, wf_tp_alg E tp_top

with wf_decl_alg : env -> decl -> Prop :=
  | wf_decl_alg_tp : forall E S U,
     wf_tp_alg E S ->
     wf_tp_alg E U ->
     wf_decl_alg E (decl_tp S U)
  | wf_decl_alg_tm : forall E T,
     wf_tp_alg E T ->
     wf_decl_alg E (decl_tm T).



Scheme typing_alg_indm   := Induction for typing_alg    Sort Prop
  with path_eq_alg_indm  := Induction for path_eq_alg   Sort Prop
  with wf_env_alg_indm   := Induction for wf_env_alg    Sort Prop
  with sub_tp_alg_indm   := Induction for sub_tp_alg    Sort Prop
  with sub_decl_alg_indm := Induction for sub_decl_alg  Sort Prop
  with wf_tp_alg_indm    := Induction for wf_tp_alg     Sort Prop
  with wf_decl_alg_indm  := Induction for wf_decl_alg   Sort Prop.
  
Combined Scheme typing_alg_mutind from typing_alg_indm, path_eq_alg_indm, wf_env_alg_indm, sub_tp_alg_indm, sub_decl_alg_indm, wf_tp_alg_indm.