(** The DOT calculus -- Syntax. *)

Require Export Dot_Labels.
Require Import Metatheory.

Definition loc := var.

Inductive tp : Set :=                         (* Type *)                 (* S, T, U, V *)
  | tp_sel : pt -> label -> tp                  (* type selection *)       (* p.L *)
  | tp_rfn : tp -> list (label * decl) -> tp    (* refinement *)           (* T { z => Ds } *)
  | tp_and : tp -> tp -> tp                     (* intersection type *)    (* T /\ T *)
  | tp_or  : tp -> tp -> tp                     (* union type *)           (* T \/ T *)
  | tp_top : tp                                 (* top type *)             (* ⊤ *)
  | tp_bot : tp                                 (* bottom type *)          (* ⊥ *)

with pt : Set :=                              (* Path *)                 (* p *)
                                                (* Variables *)            (* x, y, z *)
  | bvar : nat -> pt                            (* bound variable *)
  | fvar : var -> pt                            (* free variable *)
  | ref  : loc -> pt                            (* object reference *)     (* o *)
  | sel  : pt -> label -> pt                    (* selection *)            (* p.l *)

with tm : Set :=                              (* Term *)                 (* t *)
  | path : pt -> tm
  | new  : tp -> list (label * tm) -> tm -> tm  (* new instance *)         (* val x = new c; t *)
  | msg : pt -> label -> pt -> tm -> tm         (* method invocation *)    (* val x = p.m(p); t *)
  | exe : loc -> label -> tm -> tm -> tm        (* pending met. exec *)    (* val x = o.m... t; t *)

with decl : Set :=                            (* Declaration *)          (* D *)
  | decl_tp : tp -> tp -> decl                  (* type declaration *)     (* L : S .. U *)
  | decl_tm : tp -> decl                        (* value declaration *)    (* l : T *)
  | decl_mt : tp -> tp -> decl                  (* method declaration *)   (* m : S -> U *)
.

Inductive concrete : tp -> Prop :=
  | concrete_sel : forall p lc,
      concrete_label lc -> concrete (tp_sel p lc)
  | concrete_rfn : forall tc ds,
      concrete tc -> concrete (tp_rfn tc ds)
  | concrete_and : forall t1 t2,
      concrete t1 -> concrete t2 -> concrete (tp_and t1 t2)
  | concrete_top :
      concrete (tp_top)
.

Definition args := list (label * tm).
Definition decls_lst := list (label * decl).

Definition store : Set := list (loc * (tp * args)).
Definition gamma : Set := list (var * tp).
Definition env : Set := (gamma * store)%type.
Definition ctx_bind (E: env) (x: var) (T: tp) : env := match E with (g,p) => (((x ~ T) ++ g),p) end.

Coercion bvar : nat >-> pt.
Coercion fvar : var >-> pt.

(** * Automation *)
Hint Constructors tp decl tm concrete.