(*************************************************************************)
(** DOT  in Coq.    Definitions                                          *)
(** Author: Adriaan Moors, 2009                                          *)
(*************************************************************************)

Set Implicit Arguments.
Require Import List.
Require Import syntax_binding theory.
Require Import Metatheory LibTactics_sf support.
Require Import meta_pres_subst meta_weakening meta_inversion meta_binding meta_regular meta_decls.
Require Import Coq.Program.Equality.


Notation "E |= D <:DS<: D'" := (exists q, sub_decls E q D D') (at level 69).

  Lemma sub_decls_monotone_or_2 : forall E DS DS' DX DX' DSX DSX', 
    E |= DS <:DS<: DS' ->     E |= DX <:DS<: DX' -> 
    or_decls DS  DX DSX -> or_decls DS' DX' DSX' -> 
    E |= DSX <:DS<: DSX'.
    Proof. Admitted.

  Lemma sub_decls_monotone_and_2 : forall E DS DS' DX DX' DSX DSX', 
    E |= DS <:DS<: DS' ->     E |= DX <:DS<: DX' -> 
    and_decls DS  DX DSX -> and_decls DS' DX' DSX' -> 
    E |= DSX <:DS<: DSX'.
    Proof. Admitted.

  Lemma sub_decls_monotone_and : forall E DS DS' DX DSX DSX', 
    E |= DS <:DS<: DS' -> 
    and_decls DS  DX DSX -> and_decls DS' DX DSX' -> 
    E |= DSX <:DS<: DSX'.
    Proof. Admitted.


Lemma quality_soundness_sub : forall E DS DS' T U q1 q2, 
  E |= T ~< DS @ precise -> 
  E |= T ~<: U @ q1 -> 
  E |= U ~< DS' @ q2 /\
  E |= DS <:DS<: DS'.
Proof. Admitted. 


(*
Lemma quality_soundness_sub : forall E DS DS' T U q1 q2, 
  E |= T ~< DS @ precise -> 
  sub_tp E q1 T U -> 
  E |= U ~< DS' @ q2 ->
  E |= DS <:DS<: DS'.
Proof. 
  intros E DS DS' T U q1 q2 HXp HX. generalize dependent DS'. generalize dependent U. generalize dependent q2. generalize dependent q1. dependent induction HXp.
Focus 2.
  dependent induction q1. dependent induction q2. 
  intros ? ? ? HS. inversion HS; subst; intros. 
  inversion H0; subst; eauto; intros.

  dependent induction HXp; intros ? ? ? ? ? HX; dependent induction HX; inversion HS; subst; eauto.

  set (IHHX HXp IHHXp). inversion H3; subst; eauto.
  dependent induction HS; subst.
 set (@IHHXp precise q TP0 (sub_tp_refl E TP0) DSP0 HX).
*)


(* my precise expansion is better than yours *)
Theorem quality_soundness : forall E T DS DSp, 
  (exists q, E |= T ~< DS @ q) ->  E |= T ~< DSp @ precise -> E |= DSp <:DS<: DS.
Proof. Admitted.

(*)
  intros E T DS DSp HX HXp. generalize dependent DS.
  dependent induction HXp; intros DS0 HX; inversion HX; try dependent induction H0.
(*
case RFN, RFN:
  break down merged declarations DSM, DSM0 into DSP+DS and DSP0+DS
*)
  assert (E |= DSP <:DS<: DSP0); eauto.
  apply (@sub_decls_monotone_and E DSP DSP0 DS); auto.

(* case RFN, SUB *)
  assert (E |= (tp_rfn TP DS) ~< DSM @ precise); eauto using expands_rfn.
  apply (@quality_soundness_sub E DSM DS0 (tp_rfn TP DS) U q1 q2); eauto.

(* case /\, /\*)
  dependent induction q1; dependent induction q2.
  assert (E |= DS1 <:DS<: DS0); eauto.
  assert (E |= DS2 <:DS<: DS3); eauto.
  apply (@sub_decls_monotone_and_2 E DS1 DS0 DS2 DS3); auto.

(* case /\, SUB *)
  dependent induction q1; dependent induction q2.
  assert (E |= (tp_and T1 T2) ~< DSM @ precise & precise). apply expands_and with (DS1 := DS1) (DS2 := DS2); eauto. unfold qconj in H2.
  apply (@quality_soundness_sub E DSM DS (tp_and T1 T2) U q0 q3); eauto.

(* case \/, \/*)
  dependent induction q1; dependent induction q2.
  assert (E |= DS1 <:DS<: DS0); eauto.
  assert (E |= DS2 <:DS<: DS3); eauto.
  apply (@sub_decls_monotone_or_2 E DS1 DS0 DS2 DS3); auto.

(* case \/, SUB *)
  dependent induction q1; dependent induction q2.
  assert (E |= (tp_or T1 T2) ~< DSM @ precise & precise). apply expands_or with (DS1 := DS1) (DS2 := DS2); eauto. unfold qconj in H2.
  apply (@quality_soundness_sub E DSM DS (tp_or T1 T2) U q0 q3); eauto.

(* case Top, Top/SUB*)
  dependent induction H; eauto.
  apply quality_soundness_sub with (T := tp_top) (U := U) (q1 := q1) (q2 := q2); eauto; auto using expands_top.

(* case SUB-precise, Rfn/And/Or/Top/Sub: rewrite using reflexivity of subtyping and appeal to quality_soundness_sub *)
Hint Constructors expands. Hint Constructors sub_tp.
  dependent induction q1. dependent induction q2.
  apply quality_soundness_sub with (T := (tp_rfn TP DS0)) (U := (tp_rfn TP DS0)) (q1 := precise) (q2 := q); eauto.
  assert ( E |= (tp_rfn TP DS0) ~< DS @ (precise & precise) ); eauto.

  dependent induction q1. dependent induction q2.
  apply quality_soundness_sub with (T := (tp_and T1 T2)) (U := (tp_and T1 T2)) (q1 := precise) (q2 := q0 & q3); eauto.
  assert ( E |= (tp_and T1 T2) ~< DS @ (precise & precise) ); eauto. 

  dependent induction q1. dependent induction q2.
  apply quality_soundness_sub with (T := (tp_or T1 T2)) (U := (tp_or T1 T2)) (q1 := precise) (q2 := q0 & q3); eauto.
  assert ( E |= (tp_or T1 T2) ~< DS @ (precise & precise) ); eauto. 

  dependent induction q1. dependent induction q2.
  apply quality_soundness_sub with (T := (tp_top)) (U := (tp_top)) (q1 := precise) (q2 := precise); eauto.
  assert ( E |= (tp_top) ~< DS @ (precise & precise) ); eauto. 

  dependent induction q1. dependent induction q2.
  apply quality_soundness_sub with (T := T) (U := T) (q1 := precise) (q2 := q0 & q3); eauto.
  assert ( E |= T ~< DS @ (precise & precise) ); eauto. 
Qed.
*)

(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "../metalib") ***
*** End: ***
*)  