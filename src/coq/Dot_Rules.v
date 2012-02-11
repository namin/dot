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
(** * #<a name="wf"></a># Well-formedness *)

