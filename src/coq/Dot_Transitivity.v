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
        eauto 3 ].

Lemma expansion_exists : forall E T,
  wfe_tp E T -> exists DS, E |= T ~< DS.
Proof.
  introv Hwfe. inversion Hwfe. subst. exists DT. assumption.
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

assert (E |= S' ~<: tp_sel t l) as Ht1; eauto 3.
assert (E |= tp_sel t l ~<: tp_rfn T DS) as Ht2; eauto 3.
assert (exists D_S', E |= S' ~< D_S') as Hexp_S'_e. apply expansion_exists. eauto. inversion Hexp_S'_e as [D_S' Hexp_S'].
apply sub_tp_rfn_r with (L:=L0) (DS':=D_S'); eauto 3.
apply decls_sub_transitive with (LST:=L0) (LTU:=L0) (T:=tp_sel t l) (DT:=DS'); eauto 3.
apply sub_tp_expands_decls_sub with (U:=tp_sel t l); eauto 3.
apply decls_dom_subset_transitive with (DT:=DS'); eauto 3.
apply sub_tp_expands_decls_dom_subset with (U:=tp_sel t l) (S:=S') (E:=E); eauto 3.

assert (E |= S' ~<: tp_sel t l) as Ht1; eauto 3.
assert (E |= tp_sel t l ~<: U') as Ht2; eauto 3.
skip. (* TODO *)

assert (E |= S ~<: tp_rfn TMid l) as Ht1; eauto 3.
assert (E |= tp_rfn TMid l ~<: tp_rfn T0 DS0) as Ht2; eauto 3.
assert (E |= S ~<: T0); eauto 3.
apply sub_tp_rfn_r with (L:=L) (DS':=DS'); eauto 3.
apply decls_sub_transitive with (LST:=L) (LTU:=L0) (T:=tp_rfn TMid l) (DT:=DS'0); eauto 3.
apply sub_tp_expands_decls_sub with (U:=tp_rfn TMid l); eauto 3.
apply decls_dom_subset_transitive with (DT:=DS'0); eauto 3.
apply sub_tp_expands_decls_dom_subset with (U:=tp_rfn TMid l) (S:=S) (E:=E); eauto 3.

assert (E |= tp_fun S1 S2 ~<: tp_fun TMid1 TMid2) as Ht1; eauto 3.
assert (E |= tp_fun TMid1 TMid2 ~<: tp_rfn T DS) as Ht2; eauto 3.
inversion H; subst.
apply decls_dom_subset_nil in H2.  subst.
apply sub_tp_rfn_r with (L:=L) (DS':=decls_fin nil); eauto 3.

(* E |= tp_fun S1 S2 ~<: tp_top *)
assert (E |= tp_fun S1 S2 ~<: tp_fun TMid1 TMid2) as Ht1; eauto 3.

(* E |= tp_bot ~<: tp_fun T1 T2 *)
assert (E |= tp_fun S1 S2 ~<: tp_fun T1 T2) as Ht2; eauto 3.

assert (E |= T ~<: tp_and TMid1 TMid2) as Ht1; eauto 3.
assert (E |= tp_and TMid1 TMid2 ~<: tp_rfn T0 DS) as Ht2; eauto 3.
assert (E |= T ~<: T0). eauto 3.
assert (exists D_T, E |= T ~< D_T) as Hexp_T_e. apply expansion_exists. eauto. inversion Hexp_T_e as [D_T Hexp_T]. 
apply sub_tp_rfn_r with (L:=L) (DS':=D_T); eauto 3.
apply decls_sub_transitive with (LST:=L) (LTU:=L) (T:=tp_and TMid1 TMid2) (DT:=DS'); eauto 3.
apply sub_tp_expands_decls_sub with (U:=tp_and TMid1 TMid2); eauto 3.
apply decls_dom_subset_transitive with (DT:=DS'); eauto 3.
apply sub_tp_expands_decls_dom_subset with (U:=tp_and TMid1 TMid2) (S:=T) (E:=E); eauto 3.

assert (E |= T ~<: tp_or TMid1 TMid2) as Ht1; eauto 3.
assert (E |= tp_or TMid1 TMid2 ~<: tp_rfn T0 DS) as Ht2; eauto 3.
assert (E |= T ~<: T0). eauto 3.
assert (exists D_T, E |= T ~< D_T) as Hexp_T_e. apply expansion_exists. eauto. inversion Hexp_T_e as [D_T Hexp_T].
apply sub_tp_rfn_r with (L:=L) (DS':=D_T); eauto 3.
apply decls_sub_transitive with (LST:=L) (LTU:=L) (T:=tp_or TMid1 TMid2) (DT:=DS'); eauto 3.
apply sub_tp_expands_decls_sub with (U:=tp_or TMid1 TMid2); eauto 3.
apply decls_dom_subset_transitive with (DT:=DS'); eauto 3.
apply sub_tp_expands_decls_dom_subset with (U:=tp_or TMid1 TMid2) (S:=T) (E:=E); eauto 3.

assert (E |= T ~<: tp_or TMid1 TMid2) as Ht1; eauto 3.
assert (E |= tp_or TMid1 TMid2 ~<: tp_rfn T0 DS) as Ht2; eauto 3.
assert (E |= T ~<: T0). eauto 3.
assert (exists D_T, E |= T ~< D_T) as Hexp_T_e. apply expansion_exists. eauto. inversion Hexp_T_e as [D_T Hexp_T].
apply sub_tp_rfn_r with (L:=L) (DS':=D_T); eauto 3.
apply decls_sub_transitive with (LST:=L) (LTU:=L) (T:=tp_or TMid1 TMid2) (DT:=DS'); eauto 3.
apply sub_tp_expands_decls_sub with (U:=tp_or TMid1 TMid2); eauto 3.
apply decls_dom_subset_transitive with (DT:=DS'); eauto 3.
apply sub_tp_expands_decls_dom_subset with (U:=tp_or TMid1 TMid2) (S:=T) (E:=E); eauto 3.

assert (E |= T ~<: tp_top) as Ht1; eauto 3.
assert (E |= tp_top ~<: tp_rfn T0 DS) as Ht2; eauto 3.
inversion H1; subst.
apply decls_dom_subset_nil in H4. subst.
assert (exists D_T, E |= T ~< D_T) as Hexp_T_e. apply expansion_exists. eauto. inversion Hexp_T_e as [D_T Hexp_T].
apply sub_tp_rfn_r with (L:=L) (DS':=D_T); eauto 3.
apply sub_tp_expands_decls_sub with (U:=tp_top); eauto 3.
apply sub_tp_expands_decls_dom_subset with (U:=tp_top) (S:=T) (E:=E); eauto 3.

Qed.