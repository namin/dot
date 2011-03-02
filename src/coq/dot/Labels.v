(* This file is distributed under the terms of the MIT License, also
   known as the X11 Licence.  A copy of this license is in the README
   file that accompanied the original distribution of this file.

   Based on code written by:
     Brian Aydemir
     Aaron Bohannon
     Arthur Charg\'eraud

   With contributions from:
     Edsko de Vries:
       uniq_reorder_1, uniq_reorder_2, binds_In_inv *)

(** remove printing ~ *)

Set Implicit Arguments.
Require Export Coq.Arith.Arith.
Require Export Coq.FSets.FSets.
Require Export Coq.Lists.List.

Require Export AssocList.
Require Export CoqEqDec.
Require Export CoqListFacts.
Require Export LibTactics.
Require Import FSetExtra CoqFSetDecide.

Inductive label : Set :=
  | lv  : nat -> label   (* value label *)
  | lc  : nat -> label   (* class label *)
  | la  : nat -> label.  (* abstract type label *)

Require Import Coq.Classes.EquivDec.
Require Import Coq.Program.Program.

  
Inductive concrete_label : label -> Prop :=
  | concrete_lc : forall n, concrete_label (lc n).

(* establish decidability of label equality so we can do if then else on labels *)
Program Instance eq_label_dec : EqDec label eq :=
  { equiv_dec x y :=
    match x, y with
      | lv n, lv n' => if n == n' then in_left else in_right
      | la n, la n' => if n == n' then in_left else in_right
      | lc n, lc n' => if n == n' then in_left else in_right
      | lv n, la n' | la n, lv n' | lv n, lc n' | lc n, lv n' | la n, lc n' | lc n, la n'  => in_right (* why does wildcard pattern not work?*)
    end }.
  Obligation Tactic := unfold complement, equiv ; program_simpl.
  Solve Obligations using unfold equiv, complement in * ; program_simpl ; intuition (discriminate || eauto).


Module LabelDT <: UsualDecidableType with Definition t := label.
  Definition t := label.

  Definition eq := @eq t.
  Definition eq_refl := @refl_equal t.
  Definition eq_sym := @sym_eq t.
  Definition eq_trans := @trans_eq t.

  Definition eq_dec := eq_label_dec.
End LabelDT.


(* ********************************************************************** *)
(** * Finite sets of atoms *)

(** We use our implementation of atoms to obtain an implementation of
    finite sets of atoms.  We give the resulting type an intuitive
    name, as well as import names of set operations for use within
    this library.  In order to avoid polluting Coq's namespace, we do
    not use [Module Export]. *)

Module Import LabelSetImpl : FSetExtra.WSfun LabelDT :=
  FSetExtra.Make LabelDT.

Notation labels := LabelSetImpl.t.

(** The [AtomSetDecide] module provides the [fsetdec] tactic for
    solving facts about finite sets of atoms. *)

Module Export LabelSetDecide := CoqFSetDecide.WDecide_fun LabelDT LabelSetImpl.

(** Given the [fsetdec] tactic, we typically do not need to refer to
    specific lemmas about finite sets.  However, instantiating
    functors from the FSets library makes a number of setoid rewrites
    available.  These rewrites are crucial to developments since they
    allow us to replace a set with an extensionally equal set (see the
    [Equal] relation on finite sets) in propositions about finite
    sets. *)

Module Export LabelSetFacts := FSetFacts.WFacts_fun LabelDT LabelSetImpl.
Module LabelSetProperties := FSetProperties.WProperties_fun LabelDT LabelSetImpl.



(* ********************************************************************** *)
(** * Notations for finite sets of atoms *)

(** Common set operations and constants may be written using more
    convenient notations. *)


Notation "s [=l=] t" := (LabelSetImpl.Equal s t) (at level 70, no associativity).
Notation "s  [<l=]  t" := (LabelSetImpl.Subset s t) (at level 70, no associativity).

(*Notation "E [=] F" :=
  (AtomSetImpl.Equal E F)
  (at level 70, no associativity)
  : set_scope.

Notation "E [<=] F" :=
  (AtomSetImpl.Subset E F)
  (at level 70, no associativity)
  : set_scope.

Notation "{}" :=
  (AtomSetImpl.empty)
  : set_scope.

Notation "{{  x  }}" :=
  (AtomSetImpl.singleton x)
  : set_scope.

Notation "x `in` E" :=
  (AtomSetImpl.In x E)
  (at level 70)
  : set_hs_scope.

Notation "x `notin` E" :=
  (~ AtomSetImpl.In x E)
  (at level 70)
  : set_hs_scope.

Notation "E `union` F" :=
  (AtomSetImpl.union E F)
  (at level 65, right associativity, format "E  `union`  '/' F")
  : set_hs_scope.

(** We define some abbreviations for the empty set, singleton
    sets, and the union of two sets. *)

Notation add := AtomSetImpl.add.
Notation empty := AtomSetImpl.empty.
Notation remove := AtomSetImpl.remove.
Notation singleton := AtomSetImpl.singleton.
Notation union := AtomSetImpl.union.

(** Open the notation scopes declared above. *)

Open Scope set_scope.
Open Scope set_hs_scope.*)


(* ********************************************************************** *)
(** * Label Maps (declaration and argument lists ) *)

(** We can use our implementation of association lists (in AssocList)
    to implement association lists whose keys are atoms.  Thanks to
    parameter inlining, the types in the instantiated functor will all
    use [atom] for the type for keys. *)

Module Export LabelMapImpl := AssocList.Make LabelDT LabelSetImpl.

(** We provide alternative names for the tactics on association lists
    to reflect our use of association lists for environments. *)

Ltac simpl_labelmap := simpl_alist.

Tactic Notation "simpl_labelmap" "in" hyp(H) :=
  simpl_alist in H.

Tactic Notation "simpl_labelmap" "in" "*" :=
  simpl_alist in *.

Tactic Notation "rewrite_labelmap" constr(E) :=
  rewrite_alist E.

Tactic Notation "rewrite_labelmap" constr(E) "in" hyp(H) :=
  rewrite_alist E in H.

Tactic Notation "labelmap" "induction" ident(E) :=
  alist induction E.

Tactic Notation "labelmap" "induction" ident(E) "as" simple_intropattern(P) :=
  alist induction E as P.

(** As an alternative to the [x ~ a] notation, we also provide more
    list-like notation for writing association lists consisting of a
    single binding.

    Implementation note: The following notation overlaps with the
    standard recursive notation for lists, e.g., the one found in the
    Program library of Coq's standard library. 

Notation "[ x ]" := (EnvImpl.one x) : env_scope. 

Open Scope env_scope. *)

(* ********************************************************************** *)
(** * Lemma aliases *)

(** A number of useful lemmas are given standardized, if somewhat
    unintuitive, names.  Here, we define some intuitive aliases for
    them. *)

Notation uniq_one := uniq_one_1.
Notation uniq_cons := uniq_cons_3.
Notation uniq_app := uniq_app_4.
Notation uniq_map := uniq_map_2.

Notation binds_one := binds_one_3.
Notation binds_cons := binds_cons_3.
Notation binds_app_l := binds_app_2.
Notation binds_app_r := binds_app_3.
Notation binds_map := binds_map_2.

(*Notation notin_empty := notin_empty_1.
Notation notin_add := notin_add_3.
Notation notin_singleton := notin_singleton_2.
Notation notin_union := notin_union_3.*)


(* ********************************************************************** *)
(** * Hints *)

(** The next block of hints are occasionally useful when reasoning
    about finite sets.  In some instances, they obviate the need to
    use [auto with set]. *)

Hint Resolve
  LabelSetImpl.add_1 LabelSetImpl.add_2 LabelSetImpl.remove_1
  LabelSetImpl.remove_2 LabelSetImpl.singleton_2 LabelSetImpl.union_2
  LabelSetImpl.union_3 LabelSetImpl.inter_3 LabelSetImpl.diff_3.

