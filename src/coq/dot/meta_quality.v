(*************************************************************************)
(** DOT  in Coq.    Definitions                                          *)
(** Author: Adriaan Moors, 2009                                          *)
(*************************************************************************)

Set Implicit Arguments.
Require Import Metatheory support Dot_Definitions.
Require Import List.
Require Import Coq.Program.Equality.


Notation "E |= D <:DS<: D'" := (List.Forall (fun d => List.Exists (fun dp => exists q, sub_decl E q dp d) D) D') (at level 69).

  Lemma sub_decls_monotone_or_2 : forall E DS DS' DX DX' DSX DSX', 
    E |= DS <:DS<: DS' ->     E |= DX <:DS<: DX' -> 
    or_decls DS  DX DSX -> or_decls DS' DX' DSX' -> 
    E |= DSX <:DS<: DSX'.
    Proof.
  Admitted.

  Lemma sub_decls_monotone_and_2 : forall E DS DS' DX DX' DSX DSX', 
    E |= DS <:DS<: DS' ->     E |= DX <:DS<: DX' -> 
    and_decls DS  DX DSX -> and_decls DS' DX' DSX' -> 
    E |= DSX <:DS<: DSX'.
    Proof.
  Admitted.

  Lemma sub_decls_monotone_and : forall E DS DS' DX DSX DSX', 
    E |= DS <:DS<: DS' -> 
    and_decls DS  DX DSX -> and_decls DS' DX DSX' -> 
    E |= DSX <:DS<: DSX'.
    Proof.
  Admitted.

(* my precise expansion is better than yours *)
Theorem quality_soundness : forall E T DS DSp, 
  (exists q, E |= T ~< DS @ q) ->  E |= T ~< DSp @ precise -> E |= DSp <:DS<: DS.
Proof.
  intros E T DS DSp HX HXp. generalize dependent DS.
  dependent induction HXp; intros DS0 HX; inversion HX; try dependent induction H0.
(*
case RFN, RFN:
  break down merged declarations DSM, DSM0 into DSP+DS and DSP0+DS
*)
  assert (E |= DSP <:DS<: DSP0); eauto.
  apply (@sub_decls_monotone_and E DSP DSP0 DS); auto.

(* case /\, /\*)
  dependent induction q1; dependent induction q2.
  assert (E |= DS1 <:DS<: DS0); eauto.
  assert (E |= DS2 <:DS<: DS3); eauto.
  apply (@sub_decls_monotone_and_2 E DS1 DS0 DS2 DS3); auto.

(* case \/, \/*)
  dependent induction q1; dependent induction q2.
  assert (E |= DS1 <:DS<: DS0); eauto.
  assert (E |= DS2 <:DS<: DS3); eauto.
  apply (@sub_decls_monotone_or_2 E DS1 DS0 DS2 DS3); auto.

(* case Top, Top*)
  induction DS0; eauto.
  inversion HX. inversion H0.
Qed.

(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "../metalib") ***
*** End: ***
*)  