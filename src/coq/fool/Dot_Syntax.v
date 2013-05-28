(** The DOT calculus -- Syntax. *)

Require Export Dot_Labels.
Require Import Metatheory.

Inductive tp : Set :=                         (* Type *)                 (* S, T, U, V *)
  | tp_sel : tm -> label -> tp                  (* type selection *)       (* p.L *)
  | tp_rfn : tp -> list (label * decl) -> tp    (* refinement *)           (* T { z => Ds } *)
(*| tp_fun : tp -> tp -> tp                     (* function type *)        (* T -> T *)*)
  | tp_and : tp -> tp -> tp                     (* intersection type *)    (* T /\ T *)
  | tp_or  : tp -> tp -> tp                     (* union type *)           (* T \/ T *)
  | tp_top : tp                                 (* top type *)             (* ⊤ *)
  | tp_bot : tp                                 (* bottom type *)          (* ⊥ *)

with tm : Set :=                              (* Term *)                 (* t *)
                                                (* Variables *)            (* x, y, z *)
  | bvar : nat -> tm                            (* bound variable *)
  | fvar : var -> tm                            (* free variable *)
(*| ref  : loc -> tm                            (* object reference *)*)
(*| lam  : tp -> tm -> tm                       (* function *)             (* λx:T.t *)*)
(*| app  : tm -> tm -> tm                       (* application *)          (* t t *)*)
  | new  : tp -> list (label * tm) -> tm -> tm  (* new instance *)         (* val x = new c; t *)
  | sel  : tm -> label -> tm                    (* selection *)            (* t.l *)
  | msel : tm -> label -> tm -> tm              (* method invocation *)    (* t m t *)

with decl : Set :=                            (* Declaration *)          (* D *)
  | decl_tp : tp -> tp -> decl                  (* type declaration *)     (* L : S .. U *)
  | decl_tm : tp -> decl                        (* value declaration *)    (* l : T *)
  | decl_mt : tp -> tp -> decl                  (* method declaration *)   (* m : S -> U *)
.

Inductive path : tm -> Prop :=
  | path_bvar : forall a, path (bvar a)
  | path_fvar : forall a, path (fvar a)
  | path_sel  : forall p l, path p -> value_label l -> path (sel p l)
.

Inductive concrete : tp -> Prop :=
  | concrete_sel : forall p lc,
      path p -> concrete_label lc -> concrete (tp_sel p lc)
  | concrete_rfn : forall tc ds,
      concrete tc -> concrete (tp_rfn tc ds)
  | concrete_and : forall t1 t2,
      concrete t1 -> concrete t2 -> concrete (tp_and t1 t2)
  | concrete_top :
      concrete (tp_top)
.

Definition args := list (label * tm).
Definition decls_lst := list (label * decl).

Definition store : Set := list (var * (tp * args)).
Definition env : Set := list (var * tp).
Definition ctx_bind (E: env) (x: var) (T: tp) : env := ((x ~ T) ++ E).

Coercion bvar : nat >-> tm.
Coercion fvar : var >-> tm.

(** * Automation *)
Hint Constructors tp decl tm path concrete.