Set Implicit Arguments.
Require Import List.
Require Import syntax_binding theory.
Require Import Metatheory LibTactics_sf support meta_regular meta_binding.
Require Import Coq.Program.Equality.



(* FAILED attempts at inversion lemma for subtyping of function types:

(1)
Lemma invert_subtyping_fun : 
   (forall E q T DS, E |= T ~< DS @ q -> forall T1 T2, is_fun T T1 T2 -> DS = nil) /\
   (forall E q S T, E |= S ~<: T @ q -> forall T1 T2, is_fun S T1 T2 ->
      (exists T1', exists T2', is_fun T T1' T2' /\ (exists q, E |= T1' ~<: T1 @ q /\ exists q, E |= T2 ~<: T2' @ q))).

with subtyping including full transitivity

stuck at the sub_tp_tpsel_lower case: 
  t : E |= p ~: T' @ q1
  e : E |= T' ~< DS @ q2
  H0 : forall T1 T2 : tp, is_fun T' T1 T2 -> DS = nil
  b : lbl.binds L (decl_tp S U) DS
  H1 : is_fun (S ^tp^ p) T1 T2
  ============================
   exists T1' T2',
   is_fun (tp_sel p L) T1' T2' /\
   (exists q, E |= T1' ~<: T1 @ q /\ (exists q0, E |= T2 ~<: T2' @ q0))

--> we can't include (tp_sel p L) in is_fun (explained below)

--> add promotion to get rid of type selections?
then the problem becomes: 
  - unicity/precision of promotion
  - if we had a subderivation that E |= (S ^tp^ p) ~<: (U ^tp^ p) in the proof context (this is derivable if the store and the context are well-kinded),
we could induct and we'd be fine , but we don't have it


(2)
if we exclude type selections as the middleman in our sub_tp_trans (and expands_sub), we can prove the lemma ignoring these annoying types,
but we can't use it in preservation since we can't invert S -> T <: S' <: T' if any of those types contains a type selection...

excluding type selection is contagious: as soon as we exclude it anywhere, need to exclude it in all the cases of is_fun 
(e.g, the sub_tp_fun case requires transitivity for the components of the function type, thus, 
if transitivity excludes type selection as its middlemen, the constituents of the original function type need to exclude type selections as well)


(3)
this seems succesful so far:
have alternate subtyping/expansion relations that don't have transitivity
they also don't track quality, to avoid nested existentials in the induction hypotheses in the proof -- I cannot figure out how to make coq's automation open existentials

prove soundness and completeness wrt the original relations (where expansion has been merged into subtyping so we can induct)

*)

Reserved Notation "E |= t ~<! T" (at level 69).

(*
subtyping from a parallel universe where transitivity is unheard of; also, to simplify the proof, expansion and sub_decl are rolled into subtyping,
and quality is glossed over (need to improve my Ltac-f to bring it back: existentials must be crushed, qualities normalised), 
since inversion doesn't need to preserve quality this is not urgent, though
(inversion is why we have sub_tp_notrans in the first place -- you try inverting something with an explicit rule for transivity some time)

the order of the rules, and especially the order of the hypotheses in sub_tp_notrans_rfn_r is tuned for eauto 
as used in the proof of transitivity, sub_tp_notrans_trans (more constraining hypotheses come first) 
*)
Inductive sub_tp_notrans : env -> tp -> tp -> Prop :=
  | sub_tp_notrans_fun : forall E S1 T1 S2 T2,
      E |= S2 ~<! S1 ->
      E |= T1 ~<! T2 -> 
      E |= (tp_fun S1 T1) ~<! (tp_fun S2 T2)

  | sub_tp_notrans_tpsel_r : forall E p T' q1 DS L S U T,
      lbl.binds L (decl_tp S U) DS -> E |= T ~<! (S ^tp^ p) ->
      E |= p ~: T' @ q1 -> E |= T' ~<! (tp_rfn tp_top DS) ->
      path_safe E p ->
      E |= T ~<! (tp_sel p L)

  | sub_tp_notrans_rfn_r : forall L E T T' Tpar DSP DS DS1 DS2, (* T' = tp_top and DS1 = DS2 --> recover expands_rfn*)
      E |= T ~<! T' ->
      (* sub_decls_under L E T DS1 DS2 *) (forall z, z \notin L -> (forall l d2, lbl.binds l d2 DS2 -> exists d1, lbl.binds l d1 DS1 /\
           (forall S1 T1 S2 T2, ((d1 ^d^ z) = (decl_tp S1 T1) /\ (d2 ^d^ z) = (decl_tp S2 T2)) -> 
              (ctx_bind E z T) |= S2 ~<! S1 /\ (ctx_bind E z T) |= T1 ~<! T2 ) /\
           (forall T1 T2, ((d1 ^d^ z) = (decl_tm T1) /\ (d2 ^d^ z) = (decl_tm T2)) -> 
              (ctx_bind E z T) |= T1 ~<! T2)
          )) ->
      and_decls DSP DS DS1 ->
      E |= T ~<! (tp_rfn Tpar DS) -> E |= Tpar ~<! (tp_rfn tp_top DSP) ->  (* was E |= T ~< DS1 *)
      E |= T ~<! (tp_rfn T' DS2) 

  | sub_tp_notrans_and_r : forall E T T1 T2,
      E |= T ~<! T1 -> E |= T ~<! T2 ->
      E |= T ~<! (tp_and T1 T2)

  | expands_and : forall E T T1 DS1 T2 DS2 DSM,
      E |= T ~<! (tp_and T1 T2) ->
      E |= T1 ~<! (tp_rfn tp_top DS1) -> E |= T2 ~<! (tp_rfn tp_top DS2) -> and_decls DS1 DS2 DSM ->
      E |= T ~<! (tp_rfn tp_top DSM)

  | sub_tp_notrans_or_r1 : forall E T T1 T2,
      E |= T ~<! T1 -> 
      E |= T ~<! (tp_or T1 T2)
  | sub_tp_notrans_or_r2 : forall E T T1 T2,
      E |= T ~<! T2 -> 
      E |= T ~<! (tp_or T1 T2)

  | expands_or : forall E T T1 DS1 T2 DS2 DSM,
      E |= T ~<! (tp_or T1 T2) ->
      E |= T1 ~<! (tp_rfn tp_top DS1) -> E |= T2 ~<! (tp_rfn tp_top DS2) -> or_decls DS1 DS2 DSM ->
      E |= T ~<! (tp_rfn tp_top DSM)

  | sub_tp_notrans_refl : forall E T, E |= T ~<! T
  | sub_tp_notrans_top  : forall E T, E |= T ~<! tp_top
  | expands_top : forall E T, E |= T ~<! (tp_rfn tp_top nil)  (* see e.g, rework_sub_decls' use of sub_tp_notrans_rfn_r*)

  | sub_tp_notrans_tpsel_l : forall E p T' q1 DS L S U T,
      lbl.binds L (decl_tp S U) DS -> E |= (U ^tp^ p) ~<! T ->
      E |= p ~: T' @ q1 -> E |= T' ~<! (tp_rfn tp_top DS) -> 
      path p ->
      E |= (tp_sel p L) ~<! T

  | sub_tp_notrans_rfn_l : forall E T DS T', 
      E |= T ~<! T' -> 
      E |= (tp_rfn T DS) ~<! T'

  | sub_tp_notrans_and_l1 : forall E T T1 T2,
      E |= T1 ~<! T -> 
      E |= (tp_and T1 T2) ~<! T
  | sub_tp_notrans_and_l2 : forall E T T1 T2,
      E |= T2 ~<! T -> 
      E |= (tp_and T1 T2) ~<! T  

  | sub_tp_notrans_or_l : forall E T T1 T2,
      E |= T1 ~<! T -> E |= T2 ~<! T ->
      E |= (tp_or T1 T2) ~<! T

  | sub_tp_notrans_bot  : forall E T, E |= tp_bot ~<! T (* hide bottom down here, where it belongs *)

where "E |= T1 ~<! T2" := (sub_tp_notrans E T1 T2).

Definition sub_decls_under L E T DS1 DS2 :=
      (forall z, z \notin L -> (forall l d2, lbl.binds l d2 DS2 -> exists d1, lbl.binds l d1 DS1 /\
         (forall S1 T1 S2 T2, ((d1 ^d^ z) = (decl_tp S1 T1) /\ (d2 ^d^ z) = (decl_tp S2 T2)) -> 
            (ctx_bind E z T) |= S2 ~<! S1 /\ (ctx_bind E z T) |= T1 ~<! T2 ) /\
         (forall T1 T2, ((d1 ^d^ z) = (decl_tm T1) /\ (d2 ^d^ z) = (decl_tm T2)) -> 
            (ctx_bind E z T) |= T1 ~<! T2)
        )).



Hint Constructors sub_tp_notrans.
(*Hint Resolve sub_tp_notrans_fun sub_tp_notrans_tpsel_r sub_tp_notrans_rfn_r expands_rfn sub_tp_notrans_and_r expands_and sub_tp_notrans_or_r1 sub_tp_notrans_or_r2 expands_or sub_tp_notrans_refl sub_tp_notrans_top expands_top sub_tp_notrans_tpsel_l sub_tp_notrans_rfn_l sub_tp_notrans_and_l1 sub_tp_notrans_and_l2 sub_tp_notrans_or_l. *)

Section Soundness.
  (* TODO: deal with regularity  *)
  Lemma wf_ax : forall E, wf_env E. Proof. Admitted.
  Lemma lc_ax : forall T, lc_tp T. Proof. Admitted.
  Hint Resolve wf_ax lc_ax.

  Hint Constructors expands.
  Hint Resolve sub_tp_rfn sub_tp_rfn_elim sub_tp_tpsel_lower sub_tp_tpsel_upper sub_tp_refl sub_tp_top sub_tp_bot sub_tp_fun sub_tp_and_r sub_tp_or_l sub_tp_and_l1 sub_tp_and_l2 sub_tp_or_r1 sub_tp_or_r2. (*but not transitivity*)

  Lemma and_decls_nil: and_decls nil nil nil.            Proof. Admitted.
  Lemma and_decls_nil_1: forall DS, and_decls nil DS DS. Proof. Admitted.
  Lemma and_decls_nil_2: forall DS, and_decls DS nil DS. Proof. Admitted.
  Lemma or_decls_nil: or_decls nil nil nil.              Proof. Admitted.
  Lemma or_decls_nil_1: forall DS, or_decls nil DS nil.  Proof. Admitted.
  Lemma or_decls_nil_2: forall DS, or_decls DS nil nil.  Proof. Admitted.

  (* TODO: proof will need decls_ok from well formedness of the type that expanded to DS *)
  Lemma sub_decls_refl : forall L E DS qs T,
     forall z : atom, z `notin` L -> forall (l : label) (d2 : decl), lbl.binds l d2 DS -> exists d1, lbl.binds l d1 DS /\ 
     (exists q, In q qs /\ sub_decl (ctx_bind E z T) q (d1 ^d^ z) (d2 ^d^ z)).
  Proof. Admitted.

  Hint Resolve and_decls_nil and_decls_nil_1 and_decls_nil_2 or_decls_nil or_decls_nil_1 or_decls_nil_2 sub_decls_refl.

  (* specialize hypotheses with satisfiable embedded equalities, drop the unsatisfiable ones *)
  Ltac sphyps :=
    repeat match goal with H: ?T |- _ => 
      match T with
      | forall x, ?a = _ -> _  => 
        match type of a with
          | ?x => try (let h := fresh in lets h: H (@eq_refl x); generalizes h); clear H
        end
      | _ => generalizes H
      end
    end.
  Ltac simplhyps :=  jauto_set_hyps; intros; sphyps; intros; jauto_set_hyps; intros.

  (* TODO: how do we expose the subtyping judgements in sub_decls, so that we get an IH??
   (forall z : atom,
         z `notin` L ->
         forall (l : label) (d2 : decl),
         lbl.binds l d2 DS0 ->
         exists d1,
         lbl.binds l d1 DS1 /\
         (forall S1 T1 S2 T2 : tp,
          d1 ^d^ z = decl_tp S1 T1 /\ d2 ^d^ z = decl_tp S2 T2 ->
          ctx_bind E z T |= S2 ~<! S1 /\ ctx_bind E z T |= T1 ~<! T2) /\
         (forall T1 T2 : tp,
          d1 ^d^ z = decl_tm T1 /\ d2 ^d^ z = decl_tm T2 ->
          ctx_bind E z T |= T1 ~<! T2)) ->
     (exists qs, forall z : atom,
     z `notin` L ->
     forall (l : label) (d2 : decl),
     lbl.binds l d2 DS0 ->
     exists d1,
     lbl.binds l d1 DS1 /\
     (exists q,
      In q qs /\
      sub_decl (ctx_bind E z (tp_rfn Tpar DS)) q (d1 ^d^ z) (d2 ^d^ z)))

  *)
  Lemma notrans_is_sound : forall E T1 T2, E |= T1 ~<! T2 -> (exists q, E |= T1 ~<: T2 @ q) /\ 
    (forall DS, T2 = tp_rfn tp_top DS -> exists q, E |= T1 ~< DS @ q). 
  Proof. 
    introv H. gen E T1 T2.
     dependent induction H; (split; [ 
       simplhyps; eauto 3 | (* subtyping *)
       introv HEq; try injsubst HEq; subst;  (* expansion *)
         try destructs IHsub_tp_notrans1; try destructs IHsub_tp_notrans2; try destructs IHsub_tp_notrans; 
         simplhyps; try solve [ discriminate | eexists; intros; eauto 3] ]).

    eexists; eapply sub_tp_trans with (TMid := S ^tp^ p); eauto.

    eexists; eapply sub_tp_rfn with (DS1 := DS1) (DS2 := DS2) (qs := subsumed :: nil) (q := subsumed); eauto 3. 
    skip. (* TODO: IH for sub_decls *)
    intros; discriminate.

    forwards: (@sub_tp_rfn L E T tp_top DS1 DS0 (x & x1) subsumed (subsumed :: nil) subsumed); eauto 3.
    skip. (* TODO: IH for sub_decls *)
    intros. discriminate.
    
    eexists; eauto.

    Ltac sub_tp_rfn_top DS := eapply sub_tp_rfn with (DS1 := DS) (DS2 := DS) (qs := subsumed :: nil) (q := subsumed); eauto; intros; discriminate.

    eexists; eapply sub_tp_trans with (TMid := tp_and T1 T2); [ eauto | sub_tp_rfn_top DSM].

    eexists; eapply sub_tp_trans with (TMid := T1); eauto.

    eexists; eapply sub_tp_trans with (TMid := T2); eauto.

    eexists; eapply sub_tp_trans with (TMid := tp_or T1 T2); [eauto | sub_tp_rfn_top DSM].

    eexists; sub_tp_rfn_top (nil : decls).

    eexists; eapply sub_tp_trans with (TMid := U ^tp^ p); eauto.

    eexists; eapply sub_tp_trans with (TMid := T); eauto. 

    eexists; eapply sub_tp_trans with (TMid := T1); eauto. 

    eexists; eapply sub_tp_trans with (TMid := T2); eauto. 

    eexists; eapply expands_sub with (U := tp_rfn tp_top DS); eauto. 

    admit. (* TODO: the old system does not have an explicit rule to expand tp_bot since expands_sub subsumes to any supertype that has an expansion *)

  Admitted.
End Soundness.





(* no way this can be a rule -- the transitivity proof peterait un plomb 

not clear how i'm going to prove this... TODO: add E |== s and E |= ok judgements
*)
Lemma sub_tp_notrans_trans_tpsel : forall E q1 q2 p T DS l S U T' DS' S' U' Ta Tb,
  path_safe E p ->

  E |= p ~: T @ q1 ->
  E |= T ~<! tp_rfn tp_top DS ->
  lbl.binds l (decl_tp S U) DS ->

  E |= p ~: T' @ q2 -> 
  E |= T' ~<! tp_rfn tp_top DS' ->
  lbl.binds l (decl_tp S' U') DS' ->

  E |= Ta ~<! S ^tp^ p ->
  E |= U' ^tp^ p ~<! Tb ->

  E |= Ta ~<! Tb.
Proof. Admitted.
(*
rename t into p. rename T into Ta. rename T0 into Tb. rename T'0 into T.
rename DS0 into DS'. rename S0 into S'. rename U0 into U'.
clear IHHSubR1 IHHSubR2 IHHSubL1 IHHSubL2.

  H : path_safe E p
  H4 : E |= p ~: T' @ q0
  HSubR1 : E |= T' ~<! tp_rfn tp_top DS'
  H2 : lbl.binds l (decl_tp S' U') DS'
  HSubR2 : E |= U' ^tp^ p ~<! Tb

  H0 : E |= p ~: T @ q1
  HSubL1 : E |= T ~<! tp_rfn tp_top DS
  H1 : lbl.binds l (decl_tp S U) DS
  HSubL2 : E |= Ta ~<! S ^tp^ p

eapply sub_tp_notrans_trans_tpsel with (T' := T'); eauto.
*)



Definition transitivity_on TMid := forall E T T',  E |= T ~<! TMid -> E |= TMid ~<! T' -> E |= T ~<! T'.
Hint Unfold transitivity_on.

Lemma sub_narrowing_aux : forall TMid s F E z Sz Tz S T,
  transitivity_on TMid ->
  (E ++ z ~ (Tz, (precise, true)) ++ F, s) |= S ~<! T ->
  (E, s) |= Sz ~<! Tz ->
  (E ++ z ~ (Sz, (precise, true)) ++ F, s) |= S ~<! T.
Proof. Admitted. (*
  introv HTrans HSubL HSubZ.
  gen_eq (E ++ z ~ (Tz, (precise, true)) ++ F, s) as G. gen F.
  induction HSubL; introv EQ; subst; eauto 5.

  eapply sub_tp_notrans_tpsel_r; eauto. eapply typing_sub with (S := T').
  skip. eapply IHHSubL2; eauto.*)


Lemma narrow_sub_decls: forall L E S T DS1 DS2,  
     (forall z, z \notin L -> (forall l d2, lbl.binds l d2 DS2 -> exists d1, lbl.binds l d1 DS1 /\
           (forall S1 T1 S2 T2, ((d1 ^d^ z) = (decl_tp S1 T1) /\ (d2 ^d^ z) = (decl_tp S2 T2)) -> 
              (ctx_bind E z T) |= S2 ~<! S1 /\ (ctx_bind E z T) |= T1 ~<! T2 ) /\
           (forall T1 T2, ((d1 ^d^ z) = (decl_tm T1) /\ (d2 ^d^ z) = (decl_tm T2)) -> 
              (ctx_bind E z T) |= T1 ~<! T2)
          )) -> 
      E |=  S ~<! T ->
     (forall z, z \notin L -> (forall l d2, lbl.binds l d2 DS2 -> exists d1, lbl.binds l d1 DS1 /\
           (forall S1 T1 S2 T2, ((d1 ^d^ z) = (decl_tp S1 T1) /\ (d2 ^d^ z) = (decl_tp S2 T2)) -> 
              (ctx_bind E z S) |= S2 ~<! S1 /\ (ctx_bind E z S) |= T1 ~<! T2 ) /\
           (forall T1 T2, ((d1 ^d^ z) = (decl_tm T1) /\ (d2 ^d^ z) = (decl_tm T2)) -> 
              (ctx_bind E z S) |= T1 ~<! T2)
          )).
Proof. Admitted.

Hint Resolve narrow_sub_decls.


(* inspired by sub_transitivity from http://www.chargueraud.org/arthur/research/2007/binders/src/Fsub_Soundness.html

  Coq provides "dependent induction" to perform "Induction/inversion principle"; 4.2.1. of
   http://www.msr-inria.inria.fr/~gares/jar09.pdf explains the latter is needed to perform a proof like this
*)
Lemma sub_tp_notrans_trans : forall TMid, transitivity_on TMid.
Proof.
 introv HSubL HSubR. gen E T T'. gen_eq TMid as TMid' eq. gen TMid' eq. 
 induction TMid; intros; gen T';
   induction HSubL; try discriminate; inversions eq; intros; 
     generalize_eqs_vars HSubR; induction HSubR; simplify_dep_elim; subst; auto; try solve [ 
       eapply sub_tp_notrans_rfn_r; eauto 2; eapply narrow_sub_decls; eauto 2 |
       eapply sub_tp_notrans_and_r; eauto 2 | 
       eapply sub_tp_notrans_and_l1; eapply IHHSubL; eauto 2 |
       eapply sub_tp_notrans_and_l2; eapply IHHSubL; eauto 2 |
       eapply sub_tp_notrans_rfn_l; eapply IHHSubL; eauto 2 |
       eapply sub_tp_notrans_tpsel_l; eauto 3 using sub_tp_notrans_rfn_r |
       eapply sub_tp_notrans_or_l; eauto 3 using IHHSubL1, sub_tp_notrans_tpsel_l, IHHSubL2 |
       eapply sub_tp_notrans_rfn_r; eauto 3 using IHHSubR1, narrow_sub_decls, sub_tp_notrans_rfn_r, IHHSubR2 |
       eapply sub_tp_notrans_fun; eauto 2 using IHTMid1, IHTMid2 |
       eauto 3]. (* less than 2 minutes*)

(* admitted case:
  H2 : lbl.binds l (decl_tp S0 U0) DS0
  HSubR1 : E |= U0 ^tp^ t ~<! T0
  H3 : E |= t ~: T' @ q0
  HSubR2 : E |= T' ~<! tp_rfn tp_top DS0
  H4 : path t
  IHHSubR1 : forall (t0 : tm) (l : label),
             E |= T'0 ~<! tp_rfn tp_top DS ->
             (tp_rfn tp_top DS = tp_sel t0 l ->
              forall T' : tp, E |= tp_rfn tp_top DS ~<! T' -> E |= T'0 ~<! T') ->
             lbl.binds l (decl_tp S U) DS ->
             E |= T ~<! S ^tp^ t0 ->
             E |= t0 ~: T'0 @ q1 ->
             path_safe E t0 ->
             (S ^tp^ t0 = tp_sel t0 l ->
              forall T' : tp, E |= S ^tp^ t0 ~<! T' -> E |= T ~<! T') ->
             U0 ^tp^ t = tp_sel t0 l -> E |= T ~<! T0
  IHHSubR2 : forall (t : tm) (l : label),
             E |= T'0 ~<! tp_rfn tp_top DS ->
             (tp_rfn tp_top DS = tp_sel t l ->
              forall T' : tp, E |= tp_rfn tp_top DS ~<! T' -> E |= T'0 ~<! T') ->
             lbl.binds l (decl_tp S U) DS ->
             E |= T ~<! S ^tp^ t ->
             E |= t ~: T'0 @ q1 ->
             path_safe E t ->
             (S ^tp^ t = tp_sel t l ->
              forall T' : tp, E |= S ^tp^ t ~<! T' -> E |= T ~<! T') ->
             T' = tp_sel t l -> E |= T ~<! tp_rfn tp_top DS0
  HSubL2 : E |= T'0 ~<! tp_rfn tp_top DS
  IHHSubL2 : tp_rfn tp_top DS = tp_sel t l ->
             forall T' : tp, E |= tp_rfn tp_top DS ~<! T' -> E |= T'0 ~<! T'
  H : lbl.binds l (decl_tp S U) DS
  HSubL1 : E |= T ~<! S ^tp^ t
  H0 : E |= t ~: T'0 @ q1
  H1 : path_safe E t
  IHHSubL1 : S ^tp^ t = tp_sel t l ->
             forall T' : tp, E |= S ^tp^ t ~<! T' -> E |= T ~<! T'
  ============================
   E |= T ~<! T0
*)
 eapply sub_tp_notrans_trans_tpsel with (T' := T'); eauto.
Qed.

(*
sub_tp_notrans_or_l, sub_tp_notrans_trans_tpsel, sub_tp_notrans_trans_rfn_rfn, 
       try solve [ apply IHHSubR; eauto | 
                   apply sub_tp_notrans_or_l; eauto | 
                   eauto using rework_sub_decls |
                   eapply sub_tp_notrans_trans_tpsel with (T' := T'); eauto |
                   eapply sub_tp_notrans_trans_rfn_rfn; eauto |
                   ]. (* 7 min *)
*)

(* the motivation for the notrans version of subtyping: inversion *)
Lemma invert_fun_notrans : forall E Sa Sr Ta Tr,
  E |= tp_fun Sa Sr ~<! tp_fun Ta Tr ->
  E |= Ta ~<! Sa  /\  E |= Sr ~<! Tr.
Proof.
intros.
inverts H; splits; auto. 
Qed.




Section Completeness.

    Let P2_ (E : env) (q : quality) (S T : tp) (H: E |= S ~<: T @ q) := E |= S ~<! T.
    Let P1_ (E : env) (q : quality) (T : tp) (DS : decls) (H: E |= T ~< DS @ q) := E |= T ~<! tp_rfn tp_top DS.

    Let P0_ (E_s: env) (q: quality) (t: tm) (T: tp) (H: E_s |=  t ~: T  @ q) := True.
    Let P3_ (e : env) (q : quality) (d d0 : decl) (H: sub_decl e q d d0) := True.
    Let P4_ (e : env) (t t0 : tm) (H: path_eq e t t0) := True.
    Let P5_ (e : env) (H: wf_env e) := True.
    Let P6_ (e : env) (t : tp) (H: wf_tp e t) := True.
    Let P7_ (e : env) (d : decl) (H: wf_decl e d) := True.

  (* only hard case is sub_tp_trans, which is proven above *)
  Lemma notrans_is_complete : (forall E q S T, E |= S ~<: T @ q -> E |= S ~<! T) /\ (forall E q T DS, E |= T ~< DS @ q -> E |= T ~<! tp_rfn tp_top DS).
  Proof.
    cut ((forall E q t T (H: E |= t ~: T @ q), (@P0_ E q t T H)) /\ 
    (forall E q T DS (H: E |= T ~< DS @ q), (@P1_ E q T DS H)) /\ 
    (forall E q T T' (H: E |= T ~<: T' @ q), (@P2_  E q T T' H))  /\ 
    (forall (e : env) (q : quality) (d d0 : decl) (H : sub_decl e q d d0), (@P3_ e q d d0 H)) /\  
    (forall (e : env) (t t0 : tm) (H : path_eq e t t0), (@P4_ e t t0 H)) /\  
    (forall (e : env) (H : wf_env e), (@P5_ e H)) /\
    (forall (e : env) (t : tp) (H : wf_tp e t), (@P6_ e t H)) /\  
    (forall (e : env) (d : decl) (H : wf_decl e d), (@P7_ e d H))); [tauto | 
      apply (typing_mutind P0_ P1_ P2_ P3_ P4_ P5_ P6_ P7_); unfold P0_, P1_, P2_, P3_, P4_, P5_, P6_, P7_ in *; clear P0_ P1_ P2_ P3_ P4_ P5_ P6_ P7_]; intros; eauto 3. 

    apply sub_tp_notrans_trans with (TMid := U); eauto.
    eapply sub_tp_notrans_rfn_r; eauto. 
    skip. (* TODO: sub_decl_refl *)
    eapply sub_tp_notrans_rfn_r with (DS1 := DS1); eauto. 
    skip. (* TODO: IH for sub_decls *)
    apply and_decls_nil_1.
    apply sub_tp_notrans_trans with (TMid := TMid); eauto.
  Qed.

End NoTransSoundComplete.


(* more convenient interface to above *)
Lemma invert_expands_fun: forall E S T DS q,  E |= tp_fun S T ~< DS @ q -> DS = nil.
Proof. Admitted.


Lemma invert_expands_concrete : forall E s Tc DS q, (E, s) |= Tc ~< DS @ q -> concrete Tc -> 
    exists DS', (E, s) |= Tc ~< DS' @ precise /\ exists q, sub_decls (E, s) q DS' DS.
Proof. Admitted.


(* XXXX need to strenghten definition of E |= ok *)
Lemma sub_tp_trans_safe : forall E s S TMid T q1 q2, 
  E |== s -> (E, s) |= ok -> (E, s) |= S ~<: TMid @ q1 -> (E, s) |= TMid ~<: T @ q2 -> exists q3, (E, s) |= S ~<: T @ q3.
Proof. Admitted.  
(*
  intros.  set TMid as TMid'. dependent induction TMid; try solve [exists (q1 & q2); apply sub_tp_trans with (TMid := TMid'); auto; unfold not; intros ? ? HH; inversion HH | idtac]; clear TMid'.   
 
  destruct (regular_subtyping H1) as [HWfEnv [HLcS HLcSel]]. 
*)



Lemma expands_sub_safe : forall E s S TMid DS q1 q2, E |== s -> (E, s) |= S ~<: TMid @ q1 -> (E, s) |= TMid ~< DS @ q2 -> exists q3, (E, s) |= S ~< DS @ q3.
Proof. Admitted.



Lemma invert_typing_lam : forall E S t U q s, E |== s -> (E, s) |=  ok -> (E, s) |= lam S t ~: U @ q -> 
      exists q1, exists L, exists T, (forall x, x \notin L -> (ctx_bind (E, s) x S) |= (t ^^ x) ~: T @ q1) /\
      wf_tp (E, s) (tp_fun S T) /\ lc_tp T /\
      exists q2, (E, s) |= (tp_fun S T) ~<: U @ q2.
Proof. Admitted.

Lemma invert_typing_sel: forall E t l T q s, E |== s -> (E, s) |=  ok -> (E, s) |= sel t l ~: T @ q ->   
      exists T', exists q1, (E, s) |= t ~: T' @ q1 /\
      exists DS, exists q2, (E, s) |= T' ~< DS @ q2 /\
      exists D, lbl.binds l D DS /\
      exists S, open_decl_cond D t (decl_tm S) /\
      exists q3, (E, s) |= S ~<: T @ q3.
Proof.
  introv. intros Hstowf Hok H. dependent induction H. 
    repeat eexists; eauto. 
    destruct (regular_expands H0) as [HWfE HLcT].
    apply sub_tp_refl; auto.
      admit. (* lc_tp T where T is in opened decl *)

    destruct (IHtyping s l t E); auto. exists x. 
    destruct H1 as [q1' [HT [DS [q2' [HX [D [Hin [S0 [HOpen [q3 HSub]]]]]]]]]].
    repeat ((eapply sub_tp_trans_safe; eauto) || (esplit; eauto)).
Qed.

Lemma invert_typing_ref: forall E s a T q, (E, s) |= ref a ~: T @ q -> 
    exists T', exists args, binds a (T', args) s /\
    exists q, (E, s) |= T' ~<: T @ q.
Proof. Admitted.


Lemma invert_wf_store_uniq : forall s, wf_store s -> uniq s.
Proof. Admitted.

Lemma invert_red_store_dom : forall s t t' s', s |~ t ~~> t' ~| s' -> dom s [<=] dom s'.
Proof. Admitted.


(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "../metalib") ***
*** End: ***
*)  