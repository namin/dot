(** The DOT calculus -- Definitions *)

Require Export Dot_Labels.
Require Import Metatheory.
Require Export Dot_Syntax.

(* ********************************************************************** *)
(** * #<a name="decls"></a># Declarations *)

Definition forall_decls (E: env) (DS1: decls) (DS2: decls) (P: env -> decl -> decl -> Prop) :=
  forall l d1 d2, lbl.binds l d2 DS2 -> lbl.binds l d1 DS1 -> P E d1 d2.

Inductive valid_label : label -> decl -> Prop :=
  | valid_label_type : forall L S U, type_label L -> valid_label L (decl_tp S U)
  | valid_label_value : forall l T, value_label l -> valid_label l (decl_tm T)
.

Definition decls_ok (ds: decls) := lbl.uniq ds /\ (forall l d, lbl.binds l d ds -> valid_label l d).

Inductive and_decl : decl -> decl -> decl -> Prop :=
  | and_decl_tm : forall T1 T2,
      and_decl (decl_tm T1) (decl_tm T2) (decl_tm (tp_and T1 T2))
  | and_decl_tp : forall S1 U1 S2 U2,
      and_decl (decl_tp S1 U1) (decl_tp S2 U2) (decl_tp (tp_or S1 S2) (tp_and U1 U2))
.

Inductive or_decl : decl -> decl -> decl -> Prop :=
  | or_decl_tm : forall T1 T2,
      or_decl (decl_tm T1) (decl_tm T2) (decl_tm (tp_or T1 T2))
  | or_decl_tp : forall S1 U1 S2 U2,
      or_decl (decl_tp S1 U1) (decl_tp S2 U2) (decl_tp (tp_and S1 S2) (tp_or U1 U2))
.

Inductive bot_decl : decl -> Prop :=
  | bot_decl_tm : bot_decl (decl_tm tp_bot)
  | bot_decl_tp : bot_decl (decl_tp tp_top tp_bot)
.

Definition and_decls (ds1: decls) (ds2: decls) (dsm: decls) :=
  decls_ok dsm /\ decls_ok ds1 /\ decls_ok ds2 /\ (forall l d,
    lbl.binds l d dsm <-> (
      (exists d1, exists d2, lbl.binds l d1 ds1 /\ lbl.binds l d2 ds2 /\ and_decl d1 d2 d)
      \/ lbl.binds l d ds1 \/ lbl.binds l d ds2)).

Definition or_decls (ds1: decls) (ds2: decls) (dsm: decls) :=
  decls_ok dsm /\ decls_ok ds1 /\ decls_ok ds2 /\ (forall l d,
    lbl.binds l d dsm <-> (
      exists d1, exists d2, lbl.binds l d1 ds1 /\ lbl.binds l d2 ds2 /\ or_decl d1 d2 d)).

Definition bot_decls (dsm: decls) :=
  decls_ok dsm /\ forall l d, lbl.binds l d dsm -> bot_decl d.

(* ********************************************************************** *)
(** * #<a name="open"></a># Opening terms *)

Require Import Classes.EquivDec.

Fixpoint open_rec_tm (k : nat) (u : tm) (e : tm) {struct e} : tm :=
  match e with
    | bvar i => if k == i then u else (bvar i)
    | fvar x => fvar x
    | ref x => ref x
    | lam T b => lam (open_rec_tp k u T) (open_rec_tm (k+1) u b)
    | app f a => app (open_rec_tm k u f) (open_rec_tm k u a)
    | new T args b => new (open_rec_tp k u T) (List.map (fun a => match a with (l, a) => (l, open_rec_tm (k+1) u a) end) args) (open_rec_tm (k+1) u b)
    | sel e1 l => sel (open_rec_tm k u e1) l
  end
with open_rec_tp (k : nat) (u : tm) (t : tp) {struct t} : tp :=
  match t with
    | tp_sel e1 l => tp_sel (open_rec_tm k u e1) l
    | tp_rfn parent decls => tp_rfn (open_rec_tp k u parent) (lbl.map (open_rec_decl (k+1) u) decls)
    | tp_fun f t => tp_fun (open_rec_tp k u f) (open_rec_tp k u t)
    | tp_and t1 t2 => tp_and (open_rec_tp k u t1) (open_rec_tp k u t2)
    | tp_or t1 t2 => tp_or (open_rec_tp k u t1) (open_rec_tp k u t2)
    | tp_top => tp_top
    | tp_bot => tp_bot
  end
with open_rec_decl (k : nat) (u : tm) (d : decl) {struct d} : decl :=
  match d with
    | decl_tp tl tu => decl_tp (open_rec_tp k u tl) (open_rec_tp k u tu)
    | decl_tm t => decl_tm (open_rec_tp k u t)
  end.

Notation "{ k ~> u } t" := (open_rec_tm k u t) (at level 67).
Notation "{ k ~tp> u } t" := (open_rec_tp k u t) (at level 67).
Notation "{ k ~d> u } d" := (open_rec_decl k u d) (at level 67).
Definition open_rec_decls k u (ds: decls) := lbl.map (open_rec_decl k u) ds.
Notation "{ k ~ds> u } ds" := (open_rec_decls k u ds) (at level 67).

Definition open e u := open_rec_tm 0 u e.
Definition open_tp e u := open_rec_tp 0 u e.
Definition open_decl d u := open_rec_decl 0 u d.
Definition open_decls ds u := open_rec_decls 0 u ds.
Definition open_args (ags: args) u := lbl.map (open_rec_tm 0 u) ags.

Notation "ags ^args^ u" := (open_args ags u) (at level 67).
Notation "d ^d^ u" := (open_decl d u) (at level 67).
Notation "ds ^ds^ u" := (open_decls ds u) (at level 67).
Notation "t ^^ u" := (open t u) (at level 67).
Notation "t ^tp^ u" := (open_tp t u) (at level 67).
Notation "t ^ x" := (open t (fvar x)).

(* ********************************************************************** *)
(** * #<a name="lc"></a># Local closure *)

Inductive  lc_tp : tp -> Prop :=
  | lc_tp_sel : forall tgt l, 
      lc_tm tgt ->
      lc_tp (tp_sel tgt l)
  | lc_tp_rfn : forall L parent ds,
      lc_tp parent ->
      (forall x: atom, x \notin L -> lc_decls (ds ^ds^ x)) ->
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
  | lc_decl_tp : forall t1 t2,
      lc_tp t1 ->
      lc_tp t2 ->
      lc_decl (decl_tp t1 t2)
  | lc_decl_tm : forall t1,
      lc_tp t1 ->
      lc_decl (decl_tm t1)

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
      (forall x:var, x \notin L -> lc_args (cas ^args^ x) /\ lc_tm (b ^^ x)) ->
      lc_tm (new t cas b)
  | lc_sel : forall tgt l,
      lc_tm tgt ->
      lc_tm (sel tgt l)

with lc_decls : decls -> Prop :=
  | lc_decl_nil :
      lc_decls (nil)
  | lc_decl_cons : forall l d ds,
      lc_decl d -> lc_decls ds -> lc_decls ((l, d) :: ds)

with lc_args : args -> Prop :=
  | lc_args_nil :
      lc_args (nil)
  | lc_args_cons : forall l t cs,
      lc_tm t -> lc_args cs -> lc_args ((l, t) :: cs)
.

Inductive value : tm -> Prop := 
  | value_ref : forall l,
      value (ref l)
  | value_lam : forall t b,
      lc_tm (lam t b) -> value (lam t b)
.

Inductive syn_value : tm -> Prop :=
  | syn_value_value : forall v, value v -> syn_value v
  | syn_value_fvar  : forall v, syn_value (fvar v)
.

(* Open up decl with tm if it's a path, otherwise ensure decl is locally closed. *)
Inductive open_decl_cond : decl -> tm -> decl -> Prop :=
  | open_decl_path : forall d p,
      path p ->
      open_decl_cond d p (d ^d^ p)
  |  open_decl_term : forall d p,
      ~ path p ->
      lc_decl d ->
      open_decl_cond d p d
.

(* ********************************************************************** *)
(** * #<a name="env"></a># Environments *)

(* Locally closed, and free variables are bound in the environment/store. *)
Inductive  vars_ok_tp : env -> tp -> Prop :=
  | vars_ok_tp_sel : forall E tgt l, 
      vars_ok_tm E tgt ->
      vars_ok_tp E (tp_sel tgt l)
  | vars_ok_tp_rfn : forall E L t ds,
      vars_ok_tp E t ->
      (forall x: atom, x \notin L -> vars_ok_decls (ctx_bind E x t) (ds ^ds^ x)) ->
      vars_ok_tp E (tp_rfn t ds)
  | vars_ok_tp_fun : forall E f a,
      vars_ok_tp E f ->
      vars_ok_tp E a ->
      vars_ok_tp E (tp_fun f a)
  | vars_ok_tp_and : forall E t1 t2,
      vars_ok_tp E t1 ->
      vars_ok_tp E t2 ->
      vars_ok_tp E (tp_and t1 t2)
  | vars_ok_tp_or : forall E t1 t2,
      vars_ok_tp E t1 ->
      vars_ok_tp E t2 ->
      vars_ok_tp E (tp_or t1 t2)
  | vars_ok_tp_top : forall E, vars_ok_tp E (tp_top)
  | vars_ok_tp_bot : forall E, vars_ok_tp E (tp_bot)

with vars_ok_decl : env -> decl -> Prop :=
  | vars_ok_decl_tp : forall E t1 t2,
      vars_ok_tp E t1 ->
      vars_ok_tp E t2 ->
      vars_ok_decl E (decl_tp t1 t2)
  | vars_ok_decl_tm : forall E t1,
      vars_ok_tp E t1 ->
      vars_ok_decl E (decl_tm t1)

with vars_ok_tm : env -> tm -> Prop :=
  | vars_ok_var : forall G P x t,
      binds x t G ->
      vars_ok_tm (G, P) (fvar x)
  | vars_ok_ref : forall G P a obj,
      binds a obj P ->
      vars_ok_tm (G, P) (ref a)
  | vars_ok_lam : forall E L t b,
      vars_ok_tp E t ->
      (forall x: var, x \notin L -> vars_ok_tm (ctx_bind E x t) (b ^^ x)) ->
      vars_ok_tm E (lam t b)
  | vars_ok_app : forall E f a,
      vars_ok_tm E f ->
      vars_ok_tm E a ->
      vars_ok_tm E (app f a)
  | vars_ok_new : forall E L t cas b,
      vars_ok_tp E t ->
      (forall x: var, x \notin L -> vars_ok_args (ctx_bind E x t) (cas ^args^ x)) ->
      (forall x: var, x \notin L -> vars_ok_tm (ctx_bind E x t) (b ^^ x)) ->
      vars_ok_tm E (new t cas b)
  | vars_ok_sel : forall E tgt l,
      vars_ok_tm E tgt ->
      vars_ok_tm E (sel tgt l)

with vars_ok_decls : env -> decls -> Prop :=
  | vars_ok_decl_nil : forall E,
      vars_ok_decls E (nil)
  | vars_ok_decl_cons : forall E l d ds,
      vars_ok_decl E d -> vars_ok_decls E ds -> vars_ok_decls E ((l, d) :: ds)

with vars_ok_args : env -> args -> Prop :=
  | vars_ok_args_nil : forall E,
      vars_ok_args E (nil)
  | vars_ok_args_cons : forall E l t cs,
      vars_ok_tm E t -> vars_ok_args E cs -> vars_ok_args E ((l, t) :: cs)
.

Scheme   vars_ok_tp_indm   := Induction for vars_ok_tp Sort Prop
 with  vars_ok_decl_indm   := Induction for vars_ok_decl Sort Prop
 with    vars_ok_tm_indm   := Induction for vars_ok_tm Sort Prop
 with vars_ok_decls_indm   := Induction for vars_ok_decls Sort Prop
 with  vars_ok_args_indm   := Induction for vars_ok_args Sort Prop.

Combined Scheme vars_ok_mutind from vars_ok_tp_indm, vars_ok_decl_indm, vars_ok_tm_indm, vars_ok_decls_indm, vars_ok_args_indm.

(* ********************************************************************** *)
(** * #<a name="fv"></a># Free variables *)

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
    | tp_rfn parent decls => (fv_tp parent) \u (fold_left (fun (ats: vars) (d : (label * decl)) => ats \u (fv_decl (snd d))) decls {})
    | tp_fun f t => (fv_tp f) \u (fv_tp t)
    | tp_and t1 t2 => (fv_tp t1) \u (fv_tp t2)
    | tp_or t1 t2 => (fv_tp t1) \u (fv_tp t2)
    | tp_top => {}
    | tp_bot => {}
  end

with fv_decl (d : decl) {struct d} : vars :=
  match d with
    | decl_tp tl tu => (fv_tp tl) \u (fv_tp tu)
    | decl_tm t => fv_tp t
  end.

Definition fv_decls (decls: decls) := (fold_left (fun (ats: vars) (d : (label * decl)) => ats \u (fv_decl (snd d))) decls {}).

(* ********************************************************************** *)
(** * #<a name="subst"></a># Substitution *)

Fixpoint subst_tm (z : atom) (u : tm) (e : tm) {struct e} : tm :=
  match e with
    | bvar i => bvar i
    | ref x => if x == z then u else (ref x) (* TODO: ??? *)
    | fvar x => if x == z then u else (fvar x)
    | lam T b => lam (subst_tp z u T) (subst_tm z u b)
    | app f a => app (subst_tm z u f) (subst_tm z u a)
    | new T args b => new (subst_tp z u T) (lbl.map (subst_tm z u) args) (subst_tm z u b)
    | sel e1 l => sel (subst_tm z u e1) l
  end

with subst_tp (z : atom) (u : tm) (t : tp) {struct t} : tp :=
  match t with
    | tp_sel e1 l => tp_sel (subst_tm z u e1) l
    | tp_rfn parent decls => tp_rfn (subst_tp z u parent) (lbl.map (subst_decl z u) decls)
    | tp_fun f t => tp_fun (subst_tp z u f) (subst_tp z u t)
    | tp_and t1 t2 => tp_and (subst_tp z u t1) (subst_tp z u t2)
    | tp_or t1 t2 => tp_or (subst_tp z u t1) (subst_tp z u t2)
    | tp_top => tp_top
    | tp_bot => tp_bot
  end

with subst_decl (z : atom) (u : tm) (d : decl) {struct d} : decl :=
  match d with
    | decl_tp tl tu => decl_tp (subst_tp z u tl) (subst_tp z u tu)
    | decl_tm t => decl_tm (subst_tp z u t)
  end
.

(* ********************************************************************** *)
(** * #<a name="wf"></a># Simple well-formedness *)

Inductive wf_store : store -> Prop := 
  | wf_store_nil : wf_store nil
  | wf_store_cons_tp : forall E x Tc args,
     wf_store E ->
     (forall l v, lbl.binds l v args -> value_label l /\ value v) ->
     lc_tp Tc -> concrete Tc ->
     x \notin dom E ->
     wf_store (x ~ (Tc, args) ++ E)
.

Inductive wf_env : env -> Prop :=
  | wf_env_nil : forall P, wf_store P -> wf_env (nil, P)
  | wf_env_cons : forall G P x T,
     wf_store P ->
     wf_env (G, P) ->
     vars_ok_tp (G, P) T ->
     x `notin` dom G -> 
     wf_env ((x ~ T) ++ G, P)
.

(* ********************************************************************** *)
(** * Automation *)
Hint Constructors value.

(** * #<a name="gather_atoms"></a># The "[gather_atoms]" tactic *)
Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let C := gather_atoms_with (fun x : tm => fv_tm x) in
  let D := gather_atoms_with (fun x : tp => fv_tp x) in
  let E := gather_atoms_with (fun x : decl => fv_decl x) in
  let F := gather_atoms_with (fun x : decls => fv_decls x) in
  let G := gather_atoms_with (fun x : env => dom (fst x)) in
  constr:(A `union` B `union` C `union` D `union` E `union` F `union` G).
