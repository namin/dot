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
Coercion ref  : loc >-> tm.

Function decl_getLabel (m: decl) {struct m} : label  :=
  match m with
  | decl_tp l _ _ => l
  | decl_tm l _ => l
  end.

Require Import OrderedType OrderedTypeEx.

Module Import Nat_as_OT_Facts := OrderedTypeFacts Nat_as_OT.

Lemma eq_lab_dec : forall x y : label, { x = y } + { x <> y }.
Proof. decide equality; decide equality. Qed.

Definition same_label : decl -> decl -> Prop := fun d1 => fun d2 => (decl_getLabel d1) = (decl_getLabel d2).

(*
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



(* TODO: do we need to require lc_tm/lc_tp for constituents in path/concrete judgements? *)

Inductive path : tm -> Prop :=
  | path_ref : forall a, path (ref a)
  | path_sel : forall p l, path p -> path (sel p l).

(* open up decl with term if it's a path, otherwise ensure decl is locally closed *)
Inductive open_decl_cond : decl -> tm -> decl -> Prop :=
  | open_decl_path : forall d p,
      path p ->
      open_decl_cond d p (d ^d^ p)
  |  open_decl_term : forall d p,
      ~ path p ->
      lc_decl d -> (* D does not contain the self variable*)
      open_decl_cond d p d.

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


Inductive env_entry : Set := (* TODO *)
  | env_tp : tp -> env_entry
(*  | env_tp_ok : tp -> env_entry -- type put in context by new, which has been checked to be realizable *)
  | env_peq : (loc * label) -> env_entry.  (* track path equality a' = a.l that arises from allocating a new object referenced by a, with label l that has value a' -- if we had singleton types, we wouldn't need a new kind of binding, could just say a' : a.l.type, although duplication could be a problem since probably, for some Tc, a' : Tc *)
      
(* Definition env := EnvImpl.env env_entry. *)
Notation env := (list (atom * env_entry)).

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

Reserved Notation "E |= t ~< T @ q" (at level 69).
Reserved Notation "E |= t ~: T @ q" (at level 69).
Reserved Notation "E |= t <: T @ q" (at level 69).

Inductive value : tm -> Prop := 
  | value_ref : forall l,
    value (ref l)
  | value_lam : forall t b,
    lc_tm (lam t b) -> value (lam t b).


Section MergingMembers.
  Variable merge_decl : decl -> decl -> decl -> Prop.
  
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


Inductive typing : env -> quality -> tm -> tp -> Prop :=
   | typing_var : forall E x T,
      wf_env E ->
      lc_tp T -> (* for typing_regular *)
      binds x (env_tp T) E ->
      E |= (fvar x) ~: T @ precise

   | typing_sel : forall E q t l T,
      mem E q t (decl_tm l T) ->  
      E |= (sel t l) ~: T @ q

(* it could be simpler to  disallow chaining of subsumption by requiring a precise typing judgement;
   chained subsumption would be replaced by transitivity in the subtyping judgement
   however, member selection might need subsumed typing in order for expansion to be derivable *)
   | typing_sub : forall E q1 q2 t S T,
      E |= t ~: S @ q1->
      sub_tp E q2 S T ->
      E |= t ~: T @ q1 & q2

(* only needed for preservation: rewrite paths in case for CTX-Sel
   could factor this out to subtyping and introduce into typing by subsumption, but prefer to keep subtyping simple *)
   | typing_path_eq : forall E q t T p p', (* precise subtyping is like type equality *) 
      E |= t ~: (T ^tp^ p) @ q ->
      path_eq E p p' ->
      E |= t ~: (T ^tp^ p') @ q

(* the quality of the argument type does not contribute to the quality of the typing of the application, 
   in fact, typing of applications is entirely irrelevant since applications cannot occur in paths *)
   | typing_app : forall E q q' tf Ta Tr ta,
      E |= tf ~: (tp_fun Ta Tr) @ q ->
      E |= ta ~: Ta @ q' ->
      E |= (app tf ta) ~: Tr @ q

(* this judgement may bind a variable to an illegal type (in the environment) 
   However, a lambda with an illegal type for its argument cannot be applied, and the illegal type is confined to its body *)
   | typing_lam : forall L E q S t T,
      (forall x, x \notin L -> (x ~ (env_tp S) ++ E) |= (t ^^ x) ~: T @ q) -> (* x notin FV(T) follows from the stronger x \notin L forall L *)
      wf_tp E (tp_fun S T) ->
      E |= (lam S t) ~: (tp_fun S T) @ q

(* here, variables are bound to potentially illegal types while checking their legality, 
   when the legality is established, the variable is put in the context to type the scope of the let-binding

   T ok (legal) means the lowerbounds of all of T's type members are subtypes of their corresponding upperbounds
    
   T ok doesn't really guarantuee anything about T's value members since they may be initalised to a lambda bound variable
   nonetheless, value members either point to 
     - objects of type T' (T' ok), 
     - lambda's (irrelevant since cannot occur in paths), 
     - or variables (lambda-bound or self): 
        - for lambda-bound vars, we induct: a chain of function applications can only end if the argument is an object (or a lambda, which, again, is irrelevant)
        - self variables are assumed to have the type that's checked in this judgement, or a supertype, but T ok implies T' ok for T <: T'

   during preservation T ok holds for all bindings x : T in the environment, which precludes funny business in transitivity
   the environment only contains object references (for which store typing contains derivations that their types are OK) and path equalities
*)
   | typing_new : forall L E q Tc args t T ds,
      wf_tp E Tc ->
      concrete Tc ->
      expands E precise Tc ds ->
      (forall x, x \notin L -> 
        wf_args_decls (x ~ (env_tp Tc) ++ E) (ds ^ds^ x) args /\
        (x ~ (env_tp(*_ok*) Tc) ++ E) |= (t ^^ x) ~: T @ q) -> (* TODO: indicate that T ok holds for x : T -- needed? or is store typing enough *)
      E |= (new Tc args t) ~: T @ q


where "E |= t ~: T @ q" := (typing E q t T)

with path_eq : env -> tm -> tm -> Prop :=
   | peq_refl : forall E p, (* TODO: only needed if proof of preservation depends on it *)
      path_eq E p p

   | peq_symm : forall E p q, (* TODO: only needed if proof of preservation depends on it *)
      path_eq E p q ->
      path_eq E q p

   | peq_env : forall E a a' l,
      wf_env E ->
      binds a (env_peq (a', l)) E ->
      path_eq E (ref a) (sel a' l)

   | peq_sel : forall E p p' l T q,
      path_eq E p p' ->
      E |= (sel p l) ~: T @ q ->
      path_eq E (sel p l) (sel p' l)

(* check that lowerbounds are subtypes of upperbounds, arguments are values and they have the type declared in the decls, all value labels in decls must have corresponding arg*)
with wf_args_decls : env -> decls -> args -> Prop := 
  | wf_args_decls_tp : forall E q Tl Tu ds args l,
      sub_tp E q Tl Tu ->
      wf_args_decls E ds args ->
      wf_args_decls E ((decl_tp l Tl Tu) :: ds) args
  | wf_args_decls_tm : forall E q l v args args_rest T ds, 
      drop_tm l v args args_rest ->
      value v ->
      E |= v ~: T @ q ->
      wf_args_decls E ds args_rest ->
      wf_args_decls E ((decl_tm l T) :: ds) args
  | wf_args_decls_nil : forall E,
      wf_args_decls E nil nil

with mem : env -> quality -> tm -> decl -> Prop :=
  | mem_ : forall E q1 q2 p T D DS Dopen,
      E |= p ~: T @ q1 ->
      expands E q2 T DS ->
      In D DS ->
      open_decl_cond D p Dopen ->
      mem E (q1 & q2) p Dopen

with expands : env -> quality -> tp -> decls -> Prop := 
  | expands_rfn : forall E q TP DSP DS DSM,
      expands E q TP DSP ->
      and_decls DSP DS DSM ->
      expands E q (tp_rfn TP DS) DSM
  | expands_and : forall E q1 q2 T1 DS1 T2 DS2 DSM,
      expands E q1 T1 DS1 ->
      expands E q2 T2 DS2 ->
      and_decls DS1 DS2 DSM ->
      expands E (q1 & q2) (tp_and T1 T2) DSM
  | expands_or : forall E q1 q2 T1 DS1 T2 DS2 DSM,
      expands E q1 T1 DS1 ->
      expands E q2 T2 DS2 ->
      or_decls DS1 DS2 DSM ->
      expands E (q1 & q2) (tp_or T1 T2) DSM
  | expands_top : forall E,
      expands E precise tp_top nil
  | expands_sub : forall E q1 q2 T U DS,
      sub_tp  E q1 T U ->
      expands E q2 U DS ->
      expands E (q1 & q2) T DS
where "E |= T ~< D @ q" := (expands E q T D)

with sub_tp : env -> quality -> tp -> tp -> Prop :=  (* w/o transitivity*)
  | sub_tp_rfn_intro : forall E q T DS,
      expands E q T DS -> 
      sub_tp E q T (tp_rfn T DS)

  | sub_tp_rfn_sub : forall L E q T DS1 DS2,
      (forall z, z \notin L -> sub_decls (z ~ (env_tp T) ++ E) q (DS1 ^ds^ z) (DS2 ^ds^ z)) ->
      sub_tp E q (tp_rfn T DS1) (tp_rfn T DS2)

  | sub_tp_tpsel_lower : forall E q p L S U,
      mem E q p (decl_tp L S U) ->  (* no need to further subsume bounds: membership may use subsumption which may use sub_tp_rfn_r *)
      sub_tp E subsumed S (tp_sel p L) (* path p follows from implicit requirement that only well-formed types are compared by subtyping *)
(* TODO: is it sound to have `sub_tp E q S (tp_sel p L)` ?? *)

  | sub_tp_tpsel_upper : forall E q p L S U,
      mem E q p (decl_tp L S U) ->  (* no need to further subsume bounds: membership may use subsumption which may use sub_tp_rfn_r *)
      sub_tp E q (tp_sel p L) U (* path p follows from implicit requirement that only well-formed types are compared by subtyping *)

(* below --> not interesting: reflexivity (precise!), function types, intersection, union, top and bottom *)
  | sub_tp_refl : forall E T,
      sub_tp E precise T T
  | sub_tp_trans : forall E q1 q2 T1 T2 T3,
      sub_tp E q1 T1 T2 ->
      sub_tp E q2 T2 T3 ->
      sub_tp E (q1 & q2) T1 T3
  | sub_tp_fun : forall E q1 q2 S1 S2 T1 T2,
      sub_tp E q1 S2 S1 ->
      sub_tp E q2 T1 T2 ->
      sub_tp E (q1 & q2) (tp_fun S1 T1) (tp_fun S2 T2) 
  | sub_tp_and_r : forall E q1 q2 T T1 T2,
      sub_tp E q1 T T1 ->
      sub_tp E q2 T T2 ->
      sub_tp E (q1 & q2) T (tp_and T1 T2)
  | sub_tp_and_l1 : forall E q T T1 T2,
      sub_tp E q T1 T ->
      sub_tp E subsumed (tp_and T1 T2) T
  | sub_tp_and_l2 : forall E q T T1 T2,
      sub_tp E q T2 T ->
      sub_tp E subsumed (tp_and T1 T2) T
  | sub_tp_or_l : forall E q1 q2 T T1 T2,
      sub_tp E q1 T T1 ->
      sub_tp E q2 T T2 ->
      sub_tp E (q1 & q2) (tp_or T1 T2) T
  | sub_tp_or_r1 : forall E q T T1 T2,
      sub_tp E q T T1 ->
      sub_tp E subsumed T (tp_or T1 T2) 
  | sub_tp_or_r2 : forall E q T T1 T2,
      sub_tp E q T T2 ->
      sub_tp E subsumed T (tp_or T1 T2) 
  | sub_tp_top : forall E T,
      sub_tp E subsumed T tp_top
  | sub_tp_bot : forall E T,
      sub_tp E subsumed tp_bot T

where "E |= T1 <: T2 @ q" := (sub_tp E q T1 T2)

with sub_decl : env -> quality -> decl -> decl -> Prop :=
  | sub_decl_tp : forall E q1 q2 l S1 T1 S2 T2,
(*     sub_tp E S1 T1 ->  -- subsumed by well-formedness assumption? *)
     sub_tp E q1 S2 S1 ->
     sub_tp E q2 T1 T2 ->
     sub_decl E (q1 & q2) (decl_tp l S1 T1) (decl_tp l S2 T2) 
  | sub_decl_tm : forall E q l T1 T2,
     sub_tp E q T1 T2 ->
     sub_decl E q (decl_tm l T1) (decl_tm l T2) 

with sub_decls : env -> quality -> decls -> decls -> Prop :=
  | sub_decls_precise : forall E DS1 DS2,
      List.Forall (fun d2 => List.Exists (fun d1 => sub_decl E precise d1 d2) DS1) DS2 ->
      List.Forall (fun d1 => List.Exists (fun d2 => same_label d1 d2) DS2) DS1 ->
      sub_decls E precise DS1 DS2
  | sub_decls_subsumed : forall E DS1 DS2,
      List.Forall (fun d2 => List.Exists (fun d1 => exists q, sub_decl E q d1 d2) DS1) DS2 ->
      sub_decls E subsumed DS1 DS2

with wf_env : env -> Prop := 
  | wf_env_nil : wf_env nil
  | wf_env_cons : forall E x U,
     wf_env E ->
     x \notin dom E -> 
     (forall x, x \notin dom E -> x \notin fv_tp U) -> 
     wf_env (x ~ (env_tp U) ++ E) (* TODO env_tp_new*)

(* TODO: prove wf_tp E T implies lc_tp T  *)
with wf_tp : env -> tp -> Prop :=
  | wf_rfn : forall E T DS,
      wf_tp E T ->
      (forall z, z `notin` dom E -> 
          List.Forall (wf_decl (z ~ (env_tp (tp_rfn T DS)) ++ E)) (DS ^ds^ z)) ->
      wf_tp E (tp_rfn T DS)
  | wf_lam : forall E T1 T2,
      wf_tp E T1 -> 
      wf_tp E T2 ->
      wf_tp E (tp_fun T1 T2)
  | wf_tsel : forall E q p L S U,
      path p ->
      mem E q p (decl_tp L S U) ->
      wf_tp E S -> 
      wf_tp E U ->
      wf_tp E (tp_sel p L)
  | wf_tsel_cls : forall E q p L U,
      path p ->
      mem E q p (decl_tp L tp_bot U) ->
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




(* TODO: store and store typing, reduction
Inductive store_typing

Reserved Notation "a | s ~=> b | s'" (at level 67).


Inductive red : store -> tm -> store -> tm -> Prop :=

where "a | s ~=> b | s'" := (red s a s' b).

Definition preservation := forall E q t t' T,
  E |= t ~: T  @ q->
  t ~=> t' ->
  E |= t' ~: T @ q.

Definition progress := forall t T q, 
  nil |= t ~: T @ q ->
     value t 
  \/ exists t', t ~=> t'.
*)
  


(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "../metalib") ***
*** End: ***
*)  