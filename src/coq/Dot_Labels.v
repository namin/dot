(** The DOT calculus -- Labels. *)

Require Import Metatheory.

Inductive label : Set :=
  | lv : atom -> label          (* Value label *)          (* l *)
  | lm : atom -> label          (* Method label *)         (* m *)
                                (* Type label *)           (* L *)
  | lc : atom -> label            (* class label *)          (* Lc *)
  | la : atom -> label            (* abstract type label *)  (* La *)
.

Inductive value_label : label -> Prop :=
  | value_labe_lv : forall a, value_label (lv a)
.

Inductive method_label : label -> Prop :=
  | method_label_lm : forall a, method_label (lm a)
.

Inductive type_label : label -> Prop :=
  | type_label_lc : forall a, type_label (lc a)
  | type_label_la : forall a, type_label (la a)
.

Inductive concrete_label : label -> Prop :=
  | concrete_label_lc : forall a, concrete_label (lc a)
.

Require Import Coq.Classes.EquivDec.
Require Import Coq.Program.Program.

Program Instance eq_label_dec : @EqDec label eq eq_equivalence :=
  { equiv_dec x y :=
    match x, y with
      | lv n, lv n' => if n == n' then in_left else in_right
      | lm n, lm n' => if n == n' then in_left else in_right
      | la n, la n' => if n == n' then in_left else in_right
      | lc n, lc n' => if n == n' then in_left else in_right
      | lv n, lm n' | lm n, lv n' | lv n, la n' | la n, lv n' | lv n, lc n' | lc n, lv n' | lm n, la n' | la n, lm n' | lm n, lc n' | lc n, lm n' | la n, lc n' | lc n, la n'  => in_right (* why does wildcard pattern not work?*)
    end }.
  Obligation Tactic := unfold complement, equiv ; program_simpl.
  Solve Obligations using unfold equiv, complement in * ; program_simpl ; intuition (discriminate || eauto).

Instance EqDec_label : @EqDec label eq eq_equivalence.
Proof. exact eq_label_dec. Defined.

Module LabelDT <: UsualDecidableType with Definition t := label.
  Definition t := label.

  Definition eq := @eq t.
  Definition eq_refl := @refl_equal t.
  Definition eq_sym := @sym_eq t.
  Definition eq_trans := @trans_eq t.

  Definition eq_dec := eq_label_dec.
End LabelDT.

Module Import LabelSetImpl : FSetExtra.WSfun LabelDT := FSetExtra.Make LabelDT.
Notation labels := LabelSetImpl.t.
Module Export LabelSetDecide := CoqFSetDecide.WDecide_fun LabelDT LabelSetImpl.
Module Export LabelSetFacts := FSetFacts.WFacts_fun LabelDT LabelSetImpl.
Module LabelSetProperties := FSetProperties.WProperties_fun LabelDT LabelSetImpl.

Notation "s [=l=] t" := (LabelSetImpl.Equal s t) (at level 70, no associativity).
Notation "s  [<l=]  t" := (LabelSetImpl.Subset s t) (at level 70, no associativity).

Module Export LabelMapImpl := AssocList.Make LabelDT LabelSetImpl.

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

Notation uniq_one := uniq_one_1.
Notation uniq_cons := uniq_cons_3.
Notation uniq_app := uniq_app_4.
Notation uniq_map := uniq_map_2.

Notation binds_one := binds_one_3.
Notation binds_cons := binds_cons_3.
Notation binds_app_l := binds_app_2.
Notation binds_app_r := binds_app_3.
Notation binds_map := binds_map_2.

Hint Resolve
  LabelSetImpl.add_1 LabelSetImpl.add_2 LabelSetImpl.remove_1
  LabelSetImpl.remove_2 LabelSetImpl.singleton_2 LabelSetImpl.union_2
  LabelSetImpl.union_3 LabelSetImpl.inter_3 LabelSetImpl.diff_3.

Module lbl := LabelMapImpl.
