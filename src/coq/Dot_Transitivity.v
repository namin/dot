(** The DOT calculus -- Transitivity. *)

Set Implicit Arguments.
Require Import List.
Require Export Dot_Labels.
Require Import Metatheory LibTactics_sf.
Require Export Dot_Syntax Dot_Definitions Dot_Rules Dot_Lemmas.
Require Import Coq.Program.Equality.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Logic.Decidable.

(* ********************************************************************** *)
(** ** Transitivity of Subtyping *)

Definition transitivity_on TMid := forall E T T',
  E |= T ~<: TMid -> E |= TMid ~<: T' -> E |= T ~<: T'.
Hint Unfold transitivity_on.

Hint Constructors sub_tp mem expands.

Lemma mem_uniq: forall E p L S U S' U',
  E |= p ~mem~ L ~: (decl_tp S U) ->
  E |= p ~mem~ L ~: (decl_tp S' U') ->
  S=S' /\ U=U'.
Proof.
  (* TODO *)
Admitted.

Lemma narrow_sub_decls: forall L E S T DS1 DS2,
  E |= S ~<: T ->
  (forall z, z `notin` L ->
    forall_decls (ctx_bind E z T) (DS1 ^ds^ z) (DS2 ^ds^ z) sub_decl) ->
  (forall z, z `notin` L ->
    forall_decls (ctx_bind E z S) (DS1 ^ds^ z) (DS2 ^ds^ z) sub_decl).
Proof.
  (* TODO *)
Admitted.
Hint Resolve narrow_sub_decls.

Theorem sub_tp_transitive : forall TMid, transitivity_on TMid.
Proof.

Lemma decls_sub_transitive : forall LST LTU LSU E S T DS DT DU,
  E |= S ~<: T ->
  (forall z, z `notin` LST -> forall_decls (ctx_bind E z S) (DS ^ds^ z) (DT ^ds^ z) sub_decl) ->
  (forall z, z `notin` LTU -> forall_decls (ctx_bind E z T) (DT ^ds^ z) (DU ^ds^ z) sub_decl) ->
  (forall z, z `notin` LSU -> forall_decls (ctx_bind E z S) (DS ^ds^ z) (DU ^ds^ z) sub_decl).
Proof.
  (* TODO *)
Admitted.

Lemma decls_dom_subset_transitive : forall DS DT DU : decls,
  decls_dom_subset DU DT ->  decls_dom_subset DT DS -> decls_dom_subset DU DS.
Proof.
  (* TODO *)
Admitted.

Lemma sub_tp_expands_decls_sub : forall L E S U DS DU,
  E |= S ~<: U -> E |= S ~< DS -> E |= U ~< DU ->
  (forall z, z `notin` L -> forall_decls (ctx_bind E z S) (DS ^ds^ z) (DU ^ds^ z) sub_decl).
Proof.
  (* TODO *)
Admitted.

Lemma sub_tp_expands_decls_dom_subset : forall E S U DS DU,
  E |= S ~<: U -> E |= S ~< DS -> E |= U ~< DU ->
  decls_dom_subset DU DS.
Proof.
  (* TODO *)
Admitted.

Ltac crush_rfn_r := repeat (
  match goal with
    | [ _ : forall z, z `notin` ?L' -> forall_decls (ctx_bind ?E _ ?T_Mid) (?D_T_Mid ^ds^ _) (decls_fin ?DT_ ^ds^ _) sub_decl
      |- ?E |= ?S ~<: tp_rfn ?T ?DT ] => 
    assert (E |= S ~<: T_Mid) as Htl; eauto 3;
    assert (E |= T_Mid ~<: tp_rfn T DT) as Htr; eauto 3;
    let D_S :=fresh "D_S" with Hexp_S := fresh "Hexp_S" in
    add_expands_hyp E S D_S Hexp_S;
    apply sub_tp_rfn_r with (L:=L') (DS':=D_S)
    | [ _ : forall z, z `notin` ?L' -> forall_decls (ctx_bind ?E _ ?T_Mid) (?D_T_Mid ^ds^ _) (decls_fin ?DT_ ^ds^ _) sub_decl
      |- forall z, z `notin` ?L -> forall_decls (ctx_bind ?E _ ?S) (?D_S ^ds^ _) (decls_fin ?DT_ ^ds^ _) sub_decl] =>
    apply decls_sub_transitive with (LST:=L') (LTU:=L') (T:=T_Mid) (DT:=D_T_Mid); eauto 3;
    apply sub_tp_expands_decls_sub with (U:=T_Mid); eauto 3
    | [ _ : decls_dom_subset (decls_fin ?DT_) ?D_T_Mid, _ : ?E_ |= ?S_ ~< ?D_S, _ : ?E_ |= ?T_Mid ~< ?D_T_Mid
      |- decls_dom_subset (decls_fin ?DT_) ?D_S ] =>
    apply decls_dom_subset_transitive with (DT:=D_T_Mid); eauto 3;
    apply sub_tp_expands_decls_dom_subset with (U:=T_Mid) (S:=S_) (E:=E_); eauto 3
    | [ |- _ ] => eauto 3
  end).

  introv HSubL HSubR.
  gen T T'. gen_eq TMid as TMid' eq. gen TMid' eq.
  induction TMid; intros;
    dependent induction HSubL; intros; 
      dependent induction HSubR; subst; auto; try solve [ 
        eapply sub_tp_and_r; eauto 2 | 
        eapply sub_tp_and_l1; try eapply IHHSubL; eauto 3 |
        eapply sub_tp_and_l2; try eapply IHHSubL; eauto 3 |
        eapply sub_tp_tsel_l; eauto 3 using sub_tp_rfn_r |
        eapply sub_tp_or_l; eauto 3 using IHHSubL1, sub_tp_tsel_l, IHHSubL2 |
        eapply sub_tp_fun; eauto 2 using IHTMid1, IHTMid2 |
        eapply sub_tp_rfn_l; eauto 3 using IHHSubR1, sub_tp_tsel_r, IHHSubR2 |
        eapply sub_tp_rfn_l; eauto 3 using IHHSubL, sub_tp_rfn_r |
        inversions eq |
        crush_rfn_r |
        eauto 4].

assert (E |= S' ~<: tp_sel t l) as Ht1; eauto 3.
assert (E |= tp_sel t l ~<: U') as Ht2; eauto 3.
skip. (* TODO *)

Qed.