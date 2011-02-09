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

Inductive quality : Set :=
  | precise   : quality
  | subsumed  : quality.

Function qconj (q1: quality) (q2: quality)  {struct q1} : quality :=
  match (q1, q2) with
  | (precise, precise) => precise
  | _ => subsumed
  end.
Notation "q1 & q2" := (qconj q1 q2) (at level 67).

Inductive label : Set :=
  | lv  : nat -> label   (* value label *)
  | lc  : nat -> label   (* class label *)
  | la  : nat -> label.  (* abstract type label *)


Inductive concrete_label : label -> Prop :=
  | concrete_lc : forall n, concrete_label (lc n).

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

(* is a term a path? *)
Inductive path : tm -> Prop :=
  | path_ref : forall a, path (ref a)
  | path_sel : forall p l, path p -> path (sel p l).

(* is a type concrete? *) 
Inductive concrete : tp -> Prop :=
  | concrete_sel: forall p lc,
      path p -> concrete_label lc -> concrete (tp_sel p lc)
  | concrete_rfn : forall tc ds,
      concrete tc -> concrete (tp_rfn tc ds)
  | concrete_and : forall t1 t2,
      concrete t1 -> concrete t2 -> concrete (tp_and t1 t2)
  | concrete_top : concrete (tp_top).


Definition args  := list (label * tm).
Definition decls := list decl.

Inductive env_entry : Set := (* TODO *)
  | env_tp : tp -> env_entry
(*  | env_tp_ok : tp -> env_entry -- type put in context by new, which has been checked to be realizable *)
  | env_peq : (loc * label) -> env_entry.  (* track path equality a' = a.l that arises from allocating a new object referenced by a, with label l that has value a' -- if we had singleton types, we wouldn't need a new kind of binding, could just say a' : a.l.type, although duplication could be a problem since probably, for some Tc, a' : Tc *)
      
(* Definition env := EnvImpl.env env_entry. *)
Notation env := (list (atom * env_entry)).


Coercion bvar : nat >-> tm.
Coercion fvar : var >-> tm.
Coercion ref  : loc >-> tm.

(* TODO: do we need to require lc_tm/lc_tp for constituents in path/concrete judgements? *)




(*************************)
(* operations on members *)
(*************************)

Function decl_getLabel (m: decl) {struct m} : label  :=
  match m with
  | decl_tp l _ _ => l
  | decl_tm l _ => l
  end.

(* TODO: switch to typeclass based equality? *)
Require Import OrderedType OrderedTypeEx.
Module Import Nat_as_OT_Facts := OrderedTypeFacts Nat_as_OT.
Lemma eq_lab_dec : forall x y : label, { x = y } + { x <> y }.
Proof. decide equality; decide equality. Qed.

Definition same_label : decl -> decl -> Prop := fun d1 => fun d2 => (decl_getLabel d1) = (decl_getLabel d2).


Inductive has_decl_tm : label -> tp -> decls -> Prop :=
  | has_decl_tm_match : forall l t ds,
      has_decl_tm l t ((decl_tm l t) :: ds)
  | has_decl_tm_cons : forall l l0 t t0 ds,
      has_decl_tm l t ds ->
      l0 <> l ->
      has_decl_tm l t ((decl_tm l0 t0) :: ds).

Section MergingMembers.
  Variable merge_decl : decl -> decl -> decl -> Prop.

(*
drop_merge_decl d1 d ds2 ds2rest -> ds2rest is ds2 minus its member d2 that has the same label as d1, d is the anding of d1 and d2 (if d2 does not exist, d1=d and ds2=ds2rest) 
*)
Inductive drop_merge_decl : decl -> decl -> decls -> decls -> Prop :=
  | drop_merge_decl_head : forall d1 d2 d ds2,
      merge_decl d1 d2 d -> (* merge d1 and d2 to d -- if they have the same label *)
      drop_merge_decl d1 d (d2 :: ds2) ds2
  | drop_merge_decl_cons : forall d1 d2 d ds2 ds2rest,
      (~ same_label d1 d2) ->
      drop_merge_decl d1 d ds2 ds2rest ->
      drop_merge_decl d1 d (d2 :: ds2) (d2 :: ds2rest)
  | drop_merge_decl_nil : forall d1,
      drop_merge_decl d1 d1 nil nil.

Inductive merge_decls : decls -> decls -> decls -> Prop :=
   | merge_decls_merge : forall d1 ds1 ds2 ds2rest d ds,
     drop_merge_decl d1 d ds2 ds2rest -> (* ds2rest is ds2 minus its member with the same label as d1, d is the anding of that member in ds2 with d1 (if it does not exist, d1=d and ds2=ds2rest)  *)
     merge_decls ds1 ds2rest ds -> (* induct *)
     merge_decls (d1 :: ds1) ds2 (d :: ds).

End MergingMembers.

Inductive and_decl : decl -> decl -> decl -> Prop :=
  | and_decl_tm : forall l S1 S2,
    and_decl (decl_tm l S1) (decl_tm l S2) (decl_tm l (tp_and S1 S2))
  | and_decl_tp : forall L TL1 TU1 TL2 TU2,
    and_decl (decl_tp L TL1 TU1) (decl_tp L TL2 TU2) (decl_tp L (tp_or TL1 TL2) (tp_and TU1 TU2)).

Definition and_decls := merge_decls and_decl.

Inductive or_decl : decl -> decl -> decl -> Prop :=
  | or_decl_tm : forall l S1 S2,
    or_decl (decl_tm l S1) (decl_tm l S2) (decl_tm l (tp_or S1 S2))
  | or_decl_tp : forall L TL1 TU1 TL2 TU2,
    or_decl (decl_tp L TL1 TU1) (decl_tp L TL2 TU2) (decl_tp L (tp_and TL1 TL2) (tp_or TU1 TU2)).

Definition or_decls := merge_decls or_decl.


(********************************************)
(* operations on constructor argument lists *)
(********************************************)

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
Qed.
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
Require Import Classes.EquivDec.

Fixpoint open_rec_tm (k : nat) (u : tm) (e : tm) {struct e} : tm :=
  match e with
    | bvar i => if k == i then u else (bvar i)
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


(**********************************************)
(* syntax stuff that depends on local closure *)
(**********************************************)

Inductive value : tm -> Prop := 
  | value_ref : forall l,
    value (ref l)
  | value_lam : forall t b,
    lc_tm (lam t b) -> value (lam t b).

(* open up decl with term if it's a path, otherwise ensure decl is locally closed *)
Inductive open_decl_cond : decl -> tm -> decl -> Prop :=
  | open_decl_path : forall d p,
      path p ->
      open_decl_cond d p (d ^d^ p)
  |  open_decl_term : forall d p,
      ~ path p ->
      lc_decl d -> (* D does not contain the self variable*)
      open_decl_cond d p d.




(* SCRAPS

Inductive level : Set := terms | types. -- can't figure out how to decide equality on labels if their type is indexed by their level... 

Notation "E |= x ~?: T" := (binds_tp x T E) (at level 67).

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

Function decls_lookup (l: label) (ms: decls)  {struct ms} : option decl :=
  match ms with
  | nil => None
  | m' :: E' => if eq_lab_dec l (decl_getLabel m') then (Some m') else decls_lookup l E'
  end.

Notation "mems ?: l " := (option_map mem_getClassifier (mems_lookup l mems)) (at level 67).

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

Definition MemIn (m: mem) (ms: list mem) := (In (mem_getLabel m) (map mem_getLabel ms)).
*)

(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "../metalib") ***
*** End: ***
*)  