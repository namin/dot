(*************************************************************************)
(** DOT  in Coq.    Definitions                                          *)
(** Author: Adriaan Moors, 2009                                          *)
(*************************************************************************)

Set Implicit Arguments.
Require Import Metatheory support.
Require Import List.


(** Based on the Coq tutorial at POPL 2008, see
    "Engineering Formal Metatheory", Aydemir, Charguéraud, Pierce,
    Pollack, Weirich. POPL 2008.

    Tutorial authors: Brian Aydemir and Stephanie Weirich, with help
    from Aaron Bohannon, Nate Foster, Benjamin Pierce, Jeffrey
    Vaughan, Dimitrios Vytiniotis, and Steve Zdancewic.  Adapted from
    code by Arthur Charguéraud.
*)

(*************************************************************************)


(*************************************************************************)
(** * Syntax of DOT *)
(*********************************************************************)

(*Inductive level : Set := terms | types. -- can't figure out how to decide equality on labels if their type is indexed by their level... *)

Inductive label : Set :=
  | lv  : nat -> label   (* value label *)
  | lc  : nat -> label   (* class label *)
  | la  : nat -> label.  (* abstract type label *)

Definition loc := var.

Inductive tp : Set :=
  | tp_sel    : tm -> label -> tp        (* type selection *) (*X tm must be a path *)
  | tp_rfn    : tp -> list decl  -> tp   (* refinement *)  (* variable binding is encoded in the open_rec function below*)
  | tp_fun    : tp -> tp -> tp           (* function type *)
  | tp_and    : tp -> tp -> tp           (* intersection type *)
  | tp_or     : tp -> tp -> tp           (* union type *)
  | tp_top    : tp                       (* top type *)
  | tp_bot    : tp                       (* bottom type *)
  
(* due to recursive structure, using a set to hold the members is too 
complicated -- this is more faithful to distinction between syntax and 
well-formedness anyway*)

with decl : Set :=
  | decl_tp : label -> tp -> tp -> decl (* label, lower&upper bound (kind)*)
  | decl_tm : label -> tp -> decl       (* label, type *)

with tm : Set :=
  | bvar : nat -> tm        (* bound variables *)
  | fvar : var -> tm        (* free variables *)
  | ref  : loc -> tm        (* object reference *)
  | lam  : tp -> tm -> tm   (* function *)
  | app  : tm -> tm -> tm   (* application *)
  | new  : tp -> list (label * tm) -> tm -> tm  (* val a = new c; t, 
           where a is implicit, c : tp -> list (label * tm), t : tm
           need to check tp is concrete, constructor args are values, bound variable is a loc *)
  | sel  : tm -> label -> tm.

Definition args := list (label * tm).
Definition decls := list decl.

Coercion bvar : nat >-> tm.
Coercion fvar : var >-> tm.

(*
Function lab_getIdx (l: lab) {struct l} : nat :=
  match l with
  | ltm n => n
(*  | ltp n => n*)
  end.

Function mem_getRhs (m: mem) {struct m} : option tm :=
  match m with
  | mtm _ _ o => o
  end.

Function mem_getClassifier (m: mem) {struct m} : tp :=
  match m with
  | mtm l t _ => t
  end.
*)


Function decl_getLabel (m: decl) {struct m} : label  :=
  match m with
  | decl_tp l _ _ => l
  | decl_tm l _ => l
  end.


Require Import OrderedType OrderedTypeEx.

Module Import Nat_as_OT_Facts := OrderedTypeFacts Nat_as_OT.

Lemma eq_lab_dec : forall x y : label, { x = y } + { x <> y }.
Proof.
decide equality; decide equality.
Qed.

Definition same_label : decl -> decl -> Prop := fun d1 => fun d2 =>
 (decl_getLabel d1) = (decl_getLabel d2).

Function decls_lookup (l: label) (ms: decls)  {struct ms} : option decl :=
  match ms with
  | nil => None
  | m' :: E' => if eq_lab_dec l (decl_getLabel m') then (Some m') else decls_lookup l E'
  end.


(*
Notation "mems ?: l " := (option_map mem_getClassifier (mems_lookup l mems)) (at level 67).
*)

(*************************************************************************)
(** * Opening *)
(*************************************************************************)

(** Opening replaces an index with a term. It corresponds to informal
    substitution for a bound variable, such as in the rule for beta
    reduction. Note that only "dangling" indices (those that do not
    refer to any abstraction) can be opened. Opening has no effect for
    terms that are locally closed.

    Natural numbers are just an inductive datatype with two
    constructors: O and S, defined in Coq.Init.Datatypes.
    The notation [k === i] is the decidable equality function for
    natural numbers (cf. Coq.Peano_dec.eq_nat_dec).
    This notation is defined in the [Metatheory] library.

    We make several simplifying assumptions in defining [open_rec].

    First, we assume that the argument [u] is locally closed.  This
    assumption simplifies the implementation since we do not need to
    shift indices in [u] when passing under a binder.  Second, we
    assume that this function is initially called with index zero and
    that zero is the only unbound index in the term.  This eliminates
    the need to possibly subtract one in the case of indices.

    There is no need to worry about variable capture because bound
    variables are indices.
*)

Fixpoint open_rec_tm (k : nat) (u : tm) (e : tm) {struct e} : tm :=
  match e with
    | bvar i => if k === i then u else (bvar i)
    | fvar x => fvar x
    | ref x => ref x
    | lam T b => lam T (open_rec_tm (k+1) u b)
    | app f a => app (open_rec_tm k u f) (open_rec_tm k u a)
    | new T args b => new (open_rec_tp k u T) (List.map (fun a => match a with (l, a) => (l, open_rec_tm k u a) end) args) (open_rec_tm (k+1) u b)
    | sel e1 l => sel (open_rec_tm k u e1) l
  end
with open_rec_tp (k : nat) (u : tm) (t : tp) {struct t} : tp :=
  match t with
    | tp_sel e1 l => tp_sel (open_rec_tm k u e1) l
    | tp_rfn parent decls => tp_rfn (open_rec_tp k u parent) 
           (List.map (open_rec_decl (k+1)(* go under binder (the self variable) *) u) decls)
    | tp_fun f t => tp_fun (open_rec_tp k u f) (open_rec_tp k u t)
    | tp_and t1 t2 => tp_and (open_rec_tp k u t1) (open_rec_tp k u t2)
    | tp_or t1 t2 => tp_or (open_rec_tp k u t1) (open_rec_tp k u t2)
    | tp_top => tp_top
    | tp_bot => tp_bot
  end
with open_rec_decl (k : nat) (u : tm) (d : decl) {struct d} : decl :=
  match d with
    | decl_tp l tl tu => decl_tp l (open_rec_tp k u tl) (open_rec_tp k u tu)
    | decl_tm l t => decl_tm l (open_rec_tp k u t)
  end.

(** We also define a notation for [open_rec].
*)

Notation "{ k ~> u } t" := (open_rec_tm k u t) (at level 67).
Notation "{ k ~tp> u } t" := (open_rec_tp k u t) (at level 67).
Notation "{ k ~d> u } d" := (open_rec_decl k u d) (at level 67).
Definition open_rec_decls k u ds := map (open_rec_decl k u) ds. 
Notation "{ k ~ds> u } ds" := (open_rec_decls k u ds) (at level 67).

(** Many common applications of opening replace index zero with an
    expression or variable.  The following definition provides a
    convenient shorthand for such uses.  Note that the order of
    arguments is switched relative to the definition above.  For
    example, [(open e x)] can be read as "substitute the variable [x]
    for index [0] in [e]" and "open [e] with the variable [x]."
    Recall that the coercions above let us write [x] in place of
    [(fvar x)].
*)

Definition open e u := open_rec_tm 0 u e.
Definition open_tp e u := open_rec_tp 0 u e.
Definition open_decl d u := open_rec_decl 0 u d.
Definition open_decls ds u := map (open_rec_decl 0 u) ds.



Notation "d ^d^ u" := (open_decl d u) (at level 67).
Notation "ds ^ds^ u" := (open_decls ds u) (at level 67).
Notation "t ^^ u" := (open t u) (at level 67).
Notation "t ^tp^ u" := (open_tp t u) (at level 67).
Notation "t ^ x" := (open t (fvar x)).


(*************************************************************************)
(** * Local closure *)
(*************************************************************************)

(** Recall that [tm, tp, mem] admit terms that contain unbound indices. 
    We say that a term is locally closed, 
    when no indices appearing in it are unbound.  The proposition 
    [lc e] holds when an expression [e] is locally closed.

    The inductive definition below formalizes local closure such that
    the resulting induction principle serves as the structural
    induction principle over (locally closed) expressions.  In
    particular, unlike induction for type exp, there is no case
    for bound variables.  Thus, the induction principle corresponds more
    closely to informal practice than the one arising from the
    definition of pre-terms.
*)

Inductive  lc_tp : tp -> Prop :=
  | lc_tp_sel : forall tgt l, 
      lc_tm tgt ->
      lc_tp (tp_sel tgt l)
  | lc_tp_rfn : forall L parent ds,
      lc_tp parent ->
      (forall x:var, x \notin L -> lc_decls (ds ^ds^ x)) ->
      lc_tp (tp_rfn parent ds)
  | lc_tp_fun : forall f a,
      lc_tp f ->
      lc_tp a ->
      lc_tp (tp_fun f a)
  | lc_tp_and : forall t1 t2,
      lc_tp t1 ->
      lc_tp t2 ->
      lc_tp (tp_and t1 t2)
  | lc_tp_or : forall t1 t2,
      lc_tp t1 ->
      lc_tp t2 ->
      lc_tp (tp_or t1 t2)
  | lc_tp_top : lc_tp (tp_top)
  | lc_tp_bot : lc_tp (tp_bot)

with lc_decl : decl -> Prop :=
  | lc_decl_tp : forall l t1 t2,
      lc_tp t1 ->
      lc_tp t2 ->
      lc_decl (decl_tp l t1 t2)
  | lc_decl_tm : forall l t1,
      lc_tp t1 ->
      lc_decl (decl_tm l t1)

with lc_tm : tm -> Prop :=
  | lc_var : forall x,
      lc_tm (fvar x)
  | lc_ref : forall x,
      lc_tm (ref x)
  | lc_lam : forall L t b,
      lc_tp t ->
      (forall x:var, x \notin L -> lc_tm (b ^^ x)) ->
      lc_tm (lam t b)
  | lc_app : forall f a,
      lc_tm f ->
      lc_tm a ->
      lc_tm (app f a)
  | lc_new : forall L t cas b,
      lc_tp t ->
      lc_consargs cas ->
      (forall x:var, x \notin L -> lc_tm (b ^^ x)) ->
      lc_tm (new t cas b)
  | lc_sel : forall tgt l,
      lc_tm tgt ->
      lc_tm (sel tgt l)

with lc_decls : decls -> Prop :=
  | lc_decl_nil :
      lc_decls (nil)
  | lc_decl_cons : forall d ds,
      lc_decl d -> lc_decls ds -> lc_decls (d :: ds)

with lc_consargs : args -> Prop :=
  | lc_consarg_nil :
      lc_consargs (nil)
  | lc_consarg_cons : forall l t cs,
      lc_tm t -> lc_consargs cs -> lc_consargs ((l, t) :: cs).




(*************************************************************************)
(** * Free variables *)
(*************************************************************************)

(** The function [fv], defined below, calculates the set of free
    variables in an expression.  Because we are using locally nameless
    representation, where bound variables are represented as indices,
    any name we see is a free variable of a term.  In particular, this
    makes the [abs] case simple.
*)

Fixpoint fv_tm (e : tm) {struct e} : vars :=
  match e with
    | bvar i => {}
    | fvar x => {{x}}
    | ref x => {{x}}
    | lam T b => (fv_tp T) \u (fv_tm b)
    | app f a => (fv_tm f) \u (fv_tm a)
    | new T args b => (fv_tp T) \u  (fold_left (fun (ats: vars) (l_a :  label * tm) => match l_a with (l, t) => ats \u (fv_tm t) end) args {})
    | sel e1 l => fv_tm e1
  end

with fv_tp (t : tp) {struct t} : vars :=
  match t with
    | tp_sel e1 l => fv_tm e1
    | tp_rfn parent decls => (fv_tp parent) \u (fold_left (fun (ats: vars) (d :  decl) => ats \u (fv_decl d)) decls {})
    | tp_fun f t => (fv_tp f) \u (fv_tp t)
    | tp_and t1 t2 => (fv_tp t1) \u (fv_tp t2)
    | tp_or t1 t2 => (fv_tp t1) \u (fv_tp t2)
    | tp_top => {}
    | tp_bot => {}
  end

with fv_decl (d : decl) {struct d} : vars :=
  match d with
    | decl_tp l tl tu => (fv_tp tl) \u (fv_tp tu)
    | decl_tm l t => fv_tp t
  end.


Definition fv_decls (decls: decls) := (fold_left (fun (ats: vars) (d :  decl) => ats \u (fv_decl d)) decls {}).



(* TODO: do we need to require lc_tm/lc_tp for constituents in path/concrete judgements? *)

Inductive path : tm -> Prop :=
  | path_ref : forall a, path (ref a)
  | path_sel : forall p l, path p -> path (sel p l).

Inductive concrete_label : label -> Prop :=
  | concrete_lc : forall n, concrete_label (lc n).

Inductive concrete : tp -> Prop :=
  | concrete_sel: forall p lc,
      path p -> concrete_label lc -> concrete (tp_sel p lc)
  | concrete_rfn : forall tc ds,
      concrete tc -> concrete (tp_rfn tc ds)
  | concrete_and : forall t1 t2,
      concrete t1 -> concrete t2 -> concrete (tp_and t1 t2)
  | concrete_top : concrete (tp_top).

(*

Reserved Notation "E |= T ~::Concrete" (at level 69). (* syntactic check really *)
Reserved Notation "E |= T ~< R"  (at level 69).

Reserved Notation "E |= t ~: T" (at level 69).
Reserved Notation "E |= d ~:::wf" (at level 69).
Reserved Notation "E |= d ~:::wfs" (at level 69).


Definition MemIn (m: mem) (ms: list mem) := (In (mem_getLabel m) (map mem_getLabel ms)).
*)


Inductive env_entry : Set :=
  | env_tp : tp -> env_entry
  | env_tp_new : tp -> list (label * loc) -> env_entry.  (* track path equalities that arise from the constructor arguments supplied when instantiating a concrete type. wf_env should check tp is concrete*)
      
(* Definition env := EnvImpl.env env_entry. *)
Notation env := (list (atom * env_entry)).

Inductive binds_tp : var -> tp -> env -> Prop :=
  | binds_tp_tp : forall x T E,
    binds x (env_tp T) E ->
    binds_tp x T E
  | binds_tp_new : forall x T args E,
    binds x (env_tp_new T args) E ->
    binds_tp x T E.

(*Notation "E |= x ~?: T" := (binds_tp x T E) (at level 67).*)

Inductive has_decl_tm : label -> tp -> decls -> Prop :=
  | has_decl_tm_match : forall l t ds,
      has_decl_tm l t ((decl_tm l t) :: ds)
  | has_decl_tm_cons : forall l l0 t t0 ds,
      has_decl_tm l t ds ->
      l0 <> l ->
      has_decl_tm l t ((decl_tm l0 t0) :: ds).

Inductive has_arg_tm : label -> tm -> args -> Prop :=
  | has_arg_tm_match : forall l t ds,
      has_arg_tm l t ((l, t) :: ds)
  | has_arg_tm_cons : forall l l0 t t0 ds,
      has_arg_tm l t ds ->
      l0 <> l ->
      has_arg_tm l t ((l0, t0) :: ds).
     
(* drop_tm l t as1 as2 implies ((decl_tm l t) :: as2) is the same set of arguments as as1*)
Inductive drop_tm : label -> tm -> args -> args -> Prop :=
  | drop_tm_head : forall l t ds,
      drop_tm l t ((l, t) :: ds) ds
  | drop_tm_cons : forall l l0 t t0 ds dsrest,
      drop_tm l t ds dsrest ->
      l <> l0 ->
      drop_tm l t ((l0, t0) :: ds) ((l0, t0) :: dsrest).

Hint Constructors has_arg_tm.
(*Lemma drop_tm_splices : forall l t as1 as2,
  drop_tm l t as1 as2 -> 
      (forall l2 t2, has_arg_tm l2 t2 as1 -> has_arg_tm l2 t2 ((l, t)::as2)) 
   /\ (forall l2 t2, has_arg_tm l2 t2 ((l, t)::as2) ->  has_arg_tm l2 t2 as1).
Proof.
  intros.  split; intros.
  induction H.
    auto.
    inversion H0; subst. auto.
    assert (Hrest := IHdrop_tm H6).  
    induction (eq_lab_dec l2 l); subst; auto. 
      inversion Hrest; subst; auto*. 
        repeat (apply has_arg_tm_cons;auto). 
      inversion Hrest; subst; auto*. 

  induction H. 
    auto.
    intros. inversion H0; subst. auto.
    induction (eq_lab_dec l2 l0); subst; auto.   inversion H6; subst; auto*.
    apply has_arg_tm_cons; auto*. apply IHdrop_tm. apply has_arg_tm_cons. inversion H6; subst; auto*. auto.
Qed.*)

Reserved Notation "E |= t ~: T" (at level 69).
Reserved Notation "E |= t <: T" (at level 69).

Inductive value : tm -> Prop := 
  | value_ref : forall l,
    value (ref l)
  | value_lam : forall t b,
    lc_tm (lam t b) -> value (lam t b).

(*
Inductive same_label2 : decl -> decl -> Prop :=
  | same_label2_tm : forall l T1 T2, same_label2 (decl_tm l T1) (decl_tm l T2)
  | same_label2_tp : forall l S1 T1 S2 T2, same_label2 (decl_tp l S1 T1) (decl_tp l S2 T2).

(* get a not-exhaustive error because coq does not conveniently support dependent pattern matching: http://logical.saclay.inria.fr/coq-puma/messages/571ab803c4bb644f#msg-016f3381191c5403
*)
Definition and_decl := fun (d1: decl) => fun (d2: decl) => same_label2 d1 d2 ->
  match (d1, d2) with 
  | (decl_tm l S1, decl_tm _ S2) => decl_tm l (tp_and S1 S2)
  | (decl_tp L TL1 TU1, decl_tp _ TL2 TU2) => decl_tp L (tp_or TL1 TL2) (tp_and TU1 TU2)
  end.
*)

Inductive and_decl : decl -> decl -> decl -> Prop :=
  | and_decl_tm : forall l S1 S2,
    and_decl (decl_tm l S1) (decl_tm l S2) (decl_tm l (tp_and S1 S2))
  | and_decl_tp : forall L TL1 TU1 TL2 TU2,
    and_decl (decl_tp L TL1 TU1) (decl_tp L TL2 TU2) (decl_tp L (tp_or TL1 TL2) (tp_and TU1 TU2)).

(*
drop_merge_decl d1 d ds2 ds2rest -> ds2rest is ds2 minus its member d2 that has the same label as d1, d is the anding of d1 and d2 (if d2 does not exist, d1=d and ds2=ds2rest) 
*)
Inductive drop_merge_decl : decl -> decl -> decls -> decls -> Prop :=
  | drop_merge_decl_head : forall d1 d2 d ds2,
      and_decl d1 d2 d -> (* merge d1 and d2 to d -- if they have the same label *)
      drop_merge_decl d1 d (d2 :: ds2) ds2
  | drop_merge_decl_cons : forall d1 d2 d ds2 ds2rest,
      (~ same_label d1 d2) ->
      drop_merge_decl d1 d ds2 ds2rest ->
      drop_merge_decl d1 d (d2 :: ds2) (d2 :: ds2rest)
  | drop_merge_decl_nil : forall d1,
      drop_merge_decl d1 d1 nil nil.

Inductive and_decls : decls -> decls -> decls -> Prop :=
   | and_decls_merge : forall d1 ds1 ds2 ds2rest d ds,
     drop_merge_decl d1 d ds2 ds2rest -> (* ds2rest is ds2 minus its member with the same label as d1, d is the anding of that member in ds2 with d1 (if it does not exist, d1=d and ds2=ds2rest)  *)
     and_decls ds1 ds2rest ds -> (* induct *)
     and_decls (d1 :: ds1) ds2 (d :: ds).
 
Inductive typing : env -> tm -> tp -> Prop :=
   | typing_var : forall E x T,
      wf_env E ->
      lc_tp T -> (* for typing_regular *)
      binds_tp x T E ->
      E |= (fvar x) ~: T
   | typing_sel : forall E t l T,
      mem_tm E t (decl_tm l T) ->  
      E |= (sel t l) ~: T
   | typing_sub : forall E t S T,
      E |= t ~: S ->
      sub_tp E S T ->
      E |= t ~: T
   | typing_app : forall E tf Ta Tr ta,
      E |= tf ~: (tp_fun Ta Tr) ->
      E |= ta ~: Ta ->
      E |= (app tf ta) ~: Tr
   | typing_lam : forall L E S t T,
      (forall x, x \notin L -> (x ~ (env_tp S) ++ E) |= (t ^^ x) ~: T) -> (* x notin FV(T) follows from the stronger x \notin L forall L *)
      wf_tp E (tp_fun S T) ->
      E |= (lam S t) ~: (tp_fun S T)

   | typing_new : forall L E Tc args t T ds,
      wf_tp E Tc ->
      expands E Tc ds ->
      (forall x, x \notin L -> 
        wf_args_decls (x ~ (env_tp Tc) ++ E) (ds ^ds^ x) args /\
        (x ~ (env_tp Tc) ++ E) |= (t ^^ x) ~: T) ->
      E |= (new Tc args t) ~: T

where "E |= t ~: T" := (typing E t T)

(* check lowerbounds are subtypes of upperbounds, arguments are values and they have the type declared in the decls, all value labels in decls must have corresponding arg*)
with wf_args_decls : env -> decls -> args -> Prop := 
  | wf_args_decls_tp : forall E Tl Tu ds args l,
      sub_tp E Tl Tu ->
      wf_args_decls E ds args ->
      wf_args_decls E ((decl_tp l Tl Tu) :: ds) args
  | wf_args_decls_tm : forall E l v args args_rest T ds, 
      drop_tm l v args args_rest ->
      value v ->
      E |= v ~: T ->
      wf_args_decls E ds args_rest ->
      wf_args_decls E ((decl_tm l T) :: ds) args_rest
  | wf_args_decls_nil : forall E,
      wf_args_decls E nil nil

with mem_tm : env -> tm -> decl -> Prop :=
  | mem_tm_path : forall E p T D,
      path p ->
      E |= p ~: T ->
      mem_tp E T D ->
      mem_tm E p (D ^d^ p)
  | mem_tm_tm : forall E t T D,
      E |= t ~: T ->
      mem_tp E T D -> (* might contain a bound variable if D depends on the selfvariable*)
      lc_decl D -> (* D does not contain the self variable*)
      mem_tm E t D

with mem_tp : env -> tp -> decl -> Prop :=
  | mem_tp_rfn : forall E S T DS D,
      sub_tp E S (tp_rfn T DS) ->
      In D DS ->
      mem_tp E S D
  | mem_and : forall E T D1 D2 D,
      mem_tp E T D1 ->
      mem_tp E T D2 ->
      and_decl D1 D2 D ->
      mem_tp E T D

with expands : env -> tp -> decls -> Prop := 
  | expands_rfn : forall E TP DSP DS DSM,
      expands E TP DSP ->
      and_decls DSP DS DSM ->
      expands E (tp_rfn TP DS) DSM
  | expands_tsel : forall E p L S U DS,
      path p ->
      mem_tm E p (decl_tp L S U) ->
      expands E U DS ->
      expands E (tp_sel p L) DS
  | expands_and : forall E T1 DS1 T2 DS2 DSM,
      expands E T1 DS1 ->
      expands E T2 DS2 ->
      and_decls DS1 DS2 DSM ->
      expands E (tp_and T1 T2) DSM


with sub_tp : env -> tp -> tp -> Prop :=  (* w/o transitivity*)
  | sub_tp_refl : forall E T,
      sub_tp E T T
  | sub_tp_fun : forall E S1 S2 T1 T2,
      sub_tp E S2 S1 ->
      sub_tp E T1 T2 ->
      sub_tp E (tp_fun S1 T1) (tp_fun S2 T2) 
  | sub_tp_rfn_r : forall L E S T TDS SD TD,
      sub_tp E S T ->
      mem_tp E S SD -> 
      In TD TDS -> 
      same_label SD TD ->
      (forall z, z \notin L -> sub_decl (z ~ (env_tp T) ++ E) (SD ^d^ z) (TD ^d^ z)) ->
      sub_tp E S (tp_rfn T TDS)
  | sub_tp_rfn_l : forall E S T DSS,
      sub_tp E S T ->
      sub_tp E (tp_rfn S DSS) T 
  | sub_tp_tpsel_r : forall E p L S U S2,
      path p ->
      mem_tm E p (decl_tp L S U) ->
      sub_tp E S U -> (* TODO: shouldn't this follow from the assumption that we only check subtyping of well-formed types? *)
      sub_tp E S2 S -> (* TODO: redundant since mem_tp uses sub_tp ?*)
      sub_tp E S2 (tp_sel p L)
  | sub_tp_tpsel_l : forall E p L S U U2,
      path p ->
      mem_tm E p (decl_tp L S U) ->
      sub_tp E S U -> (* TODO: shouldn't this follow from the assumption that we only check subtyping of well-formed types? *)
      sub_tp E U U2 -> (* TODO: redundant since mem_tp uses sub_tp ?*)
      sub_tp E (tp_sel p L) U2
  | sub_tp_and_r : forall E T T1 T2,
      sub_tp E T T1 ->
      sub_tp E T T2 ->
      sub_tp E T (tp_and T1 T2)
  | sub_tp_and_l1 : forall E T T1 T2,
      sub_tp E T1 T ->
      sub_tp E (tp_and T1 T2) T
  | sub_tp_and_l2 : forall E T T1 T2,
      sub_tp E T2 T ->
      sub_tp E (tp_and T1 T2) T
  | sub_tp_or_l : forall E T T1 T2,
      sub_tp E T T1 ->
      sub_tp E T T2 ->
      sub_tp E (tp_or T1 T2) T
  | sub_tp_or_r1 : forall E T T1 T2,
      sub_tp E T T1 ->
      sub_tp E T (tp_or T1 T2) 
  | sub_tp_or_r2 : forall E T T1 T2,
      sub_tp E T T2 ->
      sub_tp E T (tp_or T1 T2) 
  | sub_tp_top : forall E T,
      sub_tp E T tp_top
  | sub_tp_bot : forall E T,
      sub_tp E tp_bot T

where "E |= T1 <: T2" := (sub_tp E T1 T2)

with sub_decl : env -> decl -> decl -> Prop :=
  | sub_decl_tp : forall E l S1 T1 S2 T2,
     sub_tp E S2 S1 ->
     sub_tp E S1 T1 ->
     sub_tp E T1 T2 ->
     sub_decl E (decl_tp l S1 T1) (decl_tp l S2 T2) 
  | sub_decl_tm : forall E l T1 T2,
     sub_tp E T1 T2 ->
     sub_decl E (decl_tm l T1) (decl_tm l T2) 

with wf_env : env -> Prop := 
  | wf_env_nil : wf_env nil
  | wf_env_cons : forall E x U,
     wf_env E ->
     x \notin dom E -> 
     (forall x, x \notin dom E -> x \notin fv_tp U) -> 
     wf_env (x ~ (env_tp U) ++ E) (* TODO env_tp_new*)

(* TODO: prove wf_tp E T implies lc_tp T  *)
with wf_tp : env -> tp -> Prop :=
  | wf_rfn : forall E T D DS,
      wf_tp E T ->
      In D DS ->
      (forall z, z `notin` dom E -> 
          wf_decl (z ~ (env_tp (tp_rfn T DS)) ++ E) (D ^d^ z)) -> (* TODO does this express what we want? *) 
      wf_tp E (tp_rfn T DS)
  | wf_lam : forall E T1 T2,
      wf_tp E T1 -> 
      wf_tp E T2 ->
      wf_tp E (tp_fun T1 T2)
  | wf_tsel1 : forall E p L S U,
      path p ->
      mem_tm E p (decl_tp L S U) ->
      wf_tp E S -> 
      wf_tp E U ->
      wf_tp E (tp_sel p L)
  | wf_tsel_cls : forall E p L U,
      path p ->
      mem_tm E p (decl_tp L tp_bot U) ->
      wf_tp E (tp_sel p L)
  | wf_and : forall E T1 T2,
      wf_tp E T1 -> 
      wf_tp E T2 ->
      wf_tp E (tp_and T1 T2)
  | wf_or : forall E T1 T2,
      wf_tp E T1 -> 
      wf_tp E T2 ->
      wf_tp E (tp_or T1 T2)
  | wf_bot : forall E, wf_tp E tp_bot
  | wf_top : forall E, wf_tp E tp_top
with wf_decl : env -> decl -> Prop :=
  | wf_decl_tp : forall E L S U,
     wf_tp E S ->
     wf_tp E U ->
     wf_decl E (decl_tp L S U)
  | wf_decl_tm : forall E l T,
     wf_tp E T ->
     wf_decl E (decl_tm l T).





Reserved Notation "a ~=> b" (at level 67).

(* TODO: store *)
Inductive red : tm -> tm -> Prop :=

where "a ~=> b" := (red a b).


Definition preservation := forall E t t' T,
  E |= t ~: T ->
  t ~=> t' ->
  E |= t' ~: T.

Definition progress := forall t T, 
  nil |= t ~: T ->
     value t 
  \/ exists t', t ~=> t'.
  
  
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "../metalib") ***
*** End: ***
*)  