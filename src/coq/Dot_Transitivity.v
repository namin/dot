(** The DOT calculus -- Transitivity. *)

Set Implicit Arguments.
Require Import List.
Require Export Dot_Labels.
Require Import Metatheory LibTactics_sf.
Require Export Dot_Syntax Dot_Definitions Dot_Rules.
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

Lemma decls_dom_subset_nil: forall ds,
  decls_dom_subset (decls_fin ds) (decls_fin nil) -> ds = nil.
Proof.
  (* TODO *)
Admitted.
Hint Resolve decls_dom_subset_nil.

Lemma decls_dom_subset_refl: forall DS,
  decls_dom_subset DS DS.
Proof.
  unfold decls_dom_subset. destruct DS. unfold "[<l=]". intros a H. assumption. reflexivity.
Qed.
Hint Resolve decls_dom_subset_refl.

Lemma expansion_permutation : forall O O' q E T DS,
  Permutation.Permutation O O' -> expands O E T DS q -> expands O' E T DS q.
Proof.
  introv Hperm Hexp. gen O'.
  induction Hexp; introv Hperm; subst; eauto using Permutation.Permutation_in.
  Case "expands_and".
    apply expands_and with (DS1:=DS1) (DS2:=DS2); eauto 3 using Permutation.perm_skip.
  Case "expands_or".
    apply expands_or with (DS1:=DS1) (DS2:=DS2); eauto 3 using Permutation.perm_skip.
Qed.
Hint Resolve expansion_permutation.

Lemma expansion_weakening : forall O q E T DS T',
  expands O E T DS q -> expands (T'::O) E T DS q.
Proof.
  introv H. induction H; eauto using in_cons, Permutation.perm_swap.
Qed.
Hint Resolve expansion_weakening.

Lemma decls_ok_fin_nil : decls_ok (decls_fin nil).
Proof.
  unfolds decls_ok. split.
    unfolds decls_uniq. introv Hx. inversion Hx; inversion H; subst; auto.
    introv Hbinds. inversion Hbinds; inversion H; inversion H1; subst; inversion H0.
Qed.

Lemma expansion_decls_ok : forall O q E T DS,
  expands O E T DS q -> decls_ok DS.
Proof.
  introv H. induction H; try solve [
    apply decls_ok_fin_nil |
    inversion H0; assumption |
    inversion H1; assumption].
Qed.

Theorem sub_tp_transitive : forall TMid, transitivity_on TMid.
Proof.

  introv HSubL HSubR. gen E T T'. gen_eq TMid as TMid' eq. gen TMid' eq.
  induction TMid; intros;
    dependent induction HSubL; intros; 
      dependent induction HSubR; subst; auto; try solve [ 
        eapply sub_tp_and_r; eauto 2 | 
        eapply sub_tp_and_l1; eapply IHHSubL; eauto 2 |
        eapply sub_tp_and_l2; eapply IHHSubL; eauto 2 |
        eapply sub_tp_tsel_l; eauto 3 using sub_tp_rfn_r |
        eapply sub_tp_or_l; eauto 3 using IHHSubL1, sub_tp_tsel_l, IHHSubL2 |
        eapply sub_tp_fun; eauto 2 using IHTMid1, IHTMid2 |
        eapply sub_tp_rfn_l; eauto 3 using IHHSubR1, sub_tp_tsel_r, IHHSubR2 |
        eapply sub_tp_rfn_l; eauto 3 using IHHSubL, sub_tp_rfn_r |
        inversions eq |
        eauto 3 ].

Lemma expansion_exists : forall E T,
  (* TODO * wf_tp E T -> *)exists DS q, E |= T ~< DS @ q.
Proof.
 (* TODO *)
Admitted.

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

Lemma sub_tp_expands_decls_sub : forall qs qu L E S U DS DU,
  E |= S ~<: U -> E |= S ~< DS @ qs -> E |= U ~< DU @ qu ->
  (forall z, z `notin` L -> forall_decls (ctx_bind E z S) (DS ^ds^ z) (DU ^ds^ z) sub_decl).
Proof.
  (* TODO *)
Admitted.

Lemma sub_tp_expands_decls_dom_subset : forall qs qu E S U DS DU,
  E |= S ~<: U -> E |= S ~< DS @ qs -> E |= U ~< DU @ qu ->
  decls_dom_subset DU DS.
Proof.
  (* TODO *)
Admitted.

Lemma sub_decls_rfn : forall q L E T DS DS',
  E |= tp_rfn T DS ~< DS' @ q ->
  (forall z, z `notin` L -> forall_decls (ctx_bind E z (tp_rfn T DS)) (DS' ^ds^ z) ((decls_fin DS) ^ds^ z) sub_decl).
Proof.
  (* TODO *)
Admitted.

assert (E |= S' ~<: tp_sel t l) as Ht1; eauto 3.
assert (E |= tp_sel t l ~<: tp_rfn T DS) as Ht2; eauto 3.
assert (exists D_S' q_S', E |= S' ~< D_S' @ q_S') as Hexp_S'_ee. apply expansion_exists.
inversion Hexp_S'_ee as [D_S' Hexp_S'_e]. inversion Hexp_S'_e as [q_S' Hexp_S'].
apply sub_tp_rfn_r with (L:=L0) (q:=q_S') (DS':=D_S'); eauto 3.
apply decls_sub_transitive with (LST:=L0) (LTU:=L0) (T:=tp_sel t l) (DT:=DS'); eauto 3.
apply sub_tp_expands_decls_sub with (qs:=q_S') (qu:=q) (U:=tp_sel t l); eauto 3.
apply decls_dom_subset_transitive with (DT:=DS'); eauto 3.
apply sub_tp_expands_decls_dom_subset with (qs:=q_S') (qu:=q) (U:=tp_sel t l) (S:=S') (E:=E); eauto 3.

assert (E |= S' ~<: tp_sel t l) as Ht1; eauto 3.
assert (E |= tp_sel t l ~<: U') as Ht2; eauto 3.
skip. (* TODO *)

assert (E |= S ~<: tp_rfn TMid l) as Ht1; eauto 3.
assert (E |= tp_rfn TMid l ~<: tp_rfn T0 DS0) as Ht2; eauto 3.
assert (E |= S ~<: T0); eauto 3.
apply sub_tp_rfn_r with (L:=L) (q:=q) (DS':=DS'); eauto 3.
apply decls_sub_transitive with (LST:=L) (LTU:=L0) (T:=tp_rfn TMid l) (DT:=DS'0); eauto 3.
apply sub_tp_expands_decls_sub with (qs:=q) (qu:=q0) (U:=tp_rfn TMid l); eauto 3.
apply decls_dom_subset_transitive with (DT:=DS'0); eauto 3.
apply sub_tp_expands_decls_dom_subset with (qs:=q) (qu:=q0) (U:=tp_rfn TMid l) (S:=S) (E:=E); eauto 3.

assert (E |= tp_fun S1 S2 ~<: tp_fun TMid1 TMid2) as Ht1; eauto 3.
assert (E |= tp_fun TMid1 TMid2 ~<: tp_rfn T DS) as Ht2; eauto 3.
inversion H; subst. inversion H3.
apply decls_dom_subset_nil in H2.  subst.
apply sub_tp_rfn_r with (L:=L) (q:=complete) (DS':=decls_fin nil); eauto 3.

assert (E |= T ~<: tp_and TMid1 TMid2) as Ht1; eauto 3.
assert (E |= tp_and TMid1 TMid2 ~<: tp_rfn T0 DS) as Ht2; eauto 3.
assert (E |= T ~<: T0). eauto 3.
assert (exists D_T q_T, E |= T ~< D_T @ q_T) as Hexp_T_ee. apply expansion_exists.
inversion Hexp_T_ee as [D_T Hexp_T_e]. inversion Hexp_T_e as [q_T Hexp_T].
apply sub_tp_rfn_r with (L:=L) (q:=q_T) (DS':=D_T); eauto 3.
apply decls_sub_transitive with (LST:=L) (LTU:=L) (T:=tp_and TMid1 TMid2) (DT:=DS'); eauto 3.
apply sub_tp_expands_decls_sub with (qs:=q_T) (qu:=q) (U:=tp_and TMid1 TMid2); eauto 3.
apply decls_dom_subset_transitive with (DT:=DS'); eauto 3.
apply sub_tp_expands_decls_dom_subset with (qs:=q_T) (qu:=q) (U:=tp_and TMid1 TMid2) (S:=T) (E:=E); eauto 3.

assert (E |= T ~<: tp_or TMid1 TMid2) as Ht1; eauto 3.
assert (E |= tp_or TMid1 TMid2 ~<: tp_rfn T0 DS) as Ht2; eauto 3.
assert (E |= T ~<: T0). eauto 3.
assert (exists D_T q_T, E |= T ~< D_T @ q_T) as Hexp_T_ee. apply expansion_exists.
inversion Hexp_T_ee as [D_T Hexp_T_e]. inversion Hexp_T_e as [q_T Hexp_T].
apply sub_tp_rfn_r with (L:=L) (q:=q_T) (DS':=D_T); eauto 3.
apply decls_sub_transitive with (LST:=L) (LTU:=L) (T:=tp_or TMid1 TMid2) (DT:=DS'); eauto 3.
apply sub_tp_expands_decls_sub with (qs:=q_T) (qu:=q) (U:=tp_or TMid1 TMid2); eauto 3.
apply decls_dom_subset_transitive with (DT:=DS'); eauto 3.
apply sub_tp_expands_decls_dom_subset with (qs:=q_T) (qu:=q) (U:=tp_or TMid1 TMid2) (S:=T) (E:=E); eauto 3.

assert (E |= T ~<: tp_or TMid1 TMid2) as Ht1; eauto 3.
assert (E |= tp_or TMid1 TMid2 ~<: tp_rfn T0 DS) as Ht2; eauto 3.
assert (E |= T ~<: T0). eauto 3.
assert (exists D_T q_T, E |= T ~< D_T @ q_T) as Hexp_T_ee. apply expansion_exists.
inversion Hexp_T_ee as [D_T Hexp_T_e]. inversion Hexp_T_e as [q_T Hexp_T].
apply sub_tp_rfn_r with (L:=L) (q:=q_T) (DS':=D_T); eauto 3.
apply decls_sub_transitive with (LST:=L) (LTU:=L) (T:=tp_or TMid1 TMid2) (DT:=DS'); eauto 3.
apply sub_tp_expands_decls_sub with (qs:=q_T) (qu:=q) (U:=tp_or TMid1 TMid2); eauto 3.
apply decls_dom_subset_transitive with (DT:=DS'); eauto 3.
apply sub_tp_expands_decls_dom_subset with (qs:=q_T) (qu:=q) (U:=tp_or TMid1 TMid2) (S:=T) (E:=E); eauto 3.

assert (E |= T ~<: tp_top) as Ht1; eauto 3.
assert (E |= tp_top ~<: tp_rfn T0 DS) as Ht2; eauto 3.
inversion H; subst. inversion H3.
apply decls_dom_subset_nil in H2. subst.
assert (exists D_T q_T, E |= T ~< D_T @ q_T) as Hexp_T_ee. apply expansion_exists.
inversion Hexp_T_ee as [D_T Hexp_T_e]. inversion Hexp_T_e as [q_T Hexp_T].
apply sub_tp_rfn_r with (L:=L) (q:=q_T) (DS':=D_T); eauto 3.
apply sub_tp_expands_decls_sub with (qs:=q_T) (qu:=complete) (U:=tp_top); eauto 3.
apply sub_tp_expands_decls_dom_subset with (qs:=q_T) (qu:=complete) (U:=tp_top) (S:=T) (E:=E); eauto 3.

Qed.