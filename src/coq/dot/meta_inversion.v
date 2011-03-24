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
      and_decls DSP DS DS1 -> (* order of rules tuned for eauto*)
      E |= T ~<! (tp_rfn Tpar DS) -> E |= Tpar ~<! (tp_rfn tp_top DSP) ->  (* was E |= T ~< DS1 *)
(* or, to get rid of expands_top:
         ((Tpar <> tp_top -> (E |= Tpar ~<! (tp_rfn tp_top DSP) /\ and_decls DSP DS DS1)) /\
         (Tpar = tp_top  -> (DSP = nil /\ DS = DS1))) ->
*)

      E |= T ~<! (tp_rfn T' DS2) 


(*  | expands_rfn : forall E Tpar DSP DS DSM,
      E |= T ~<! (tp_rfn Tpar DS) ->
      E |= Tpar ~<! (tp_rfn tp_top DSP) -> and_decls DSP DS DSM ->
      E |= T ~<! (tp_rfn tp_top DSM) *)

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

  | sub_tp_notrans_bot  : forall E T, E |= tp_bot ~<! T


where "E |= T1 ~<! T2" := (sub_tp_notrans E T1 T2).

Definition sub_decls_under L E T DS1 DS2 :=
      (forall z, z \notin L -> (forall l d2, lbl.binds l d2 DS2 -> exists d1, lbl.binds l d1 DS1 /\
         (forall S1 T1 S2 T2, ((d1 ^d^ z) = (decl_tp S1 T1) /\ (d2 ^d^ z) = (decl_tp S2 T2)) -> 
            (ctx_bind E z T) |= S2 ~<! S1 /\ (ctx_bind E z T) |= T1 ~<! T2 ) /\
         (forall T1 T2, ((d1 ^d^ z) = (decl_tm T1) /\ (d2 ^d^ z) = (decl_tm T2)) -> 
            (ctx_bind E z T) |= T1 ~<! T2)
        )).



Section NoTransSoundComplete.


Tactic Notation "gen_eq" constr(c) "as" ident(x) ident(H) :=
  set (x := c); assert (H : x = c) by reflexivity; clearbody x.

Hint Constructors sub_tp_notrans.

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

Lemma strengthen_sub_decls: forall L E S T DS1 DS2,  
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

Hint Resolve strengthen_sub_decls.

(* inspired by sub_transitivity from http://www.chargueraud.org/arthur/research/2007/binders/src/Fsub_Soundness.html

  Coq provides "dependent induction" to perform "Induction/inversion principle"; 4.2.1. of
   http://www.msr-inria.inria.fr/~gares/jar09.pdf explains the latter is needed to perform a proof like this
*)
Lemma sub_tp_notrans_trans : forall E T TMid T',
  E |= T ~<! TMid -> E |= TMid ~<! T' -> E |= T ~<! T'.
Proof.
 introv HSubL HSubR. gen E T T'. gen_eq TMid as TMid' eq. gen TMid' eq. 
 induction TMid; intros TMid' EQ; intros;
   dependent induction HSubL; try discriminate; inversions EQ;
     intros; dependent induction HSubR; subst; auto; try solve [ 
       eapply sub_tp_notrans_rfn_r; eauto 2; eapply strengthen_sub_decls; eauto 2 |
       eapply sub_tp_notrans_and_r; eauto 2 | 
       eapply sub_tp_notrans_and_l1; eapply IHHSubL; eauto 2 |
       eapply sub_tp_notrans_and_l2; eapply IHHSubL; eauto 2 |
       eapply sub_tp_notrans_rfn_l; eapply IHHSubL; eauto 2 |
       eapply sub_tp_notrans_tpsel_l; eauto 3 using sub_tp_notrans_rfn_r |
       eapply sub_tp_notrans_or_l; eauto 3 using IHHSubL1, sub_tp_notrans_tpsel_l, IHHSubL2 |
       eapply sub_tp_notrans_rfn_r; eauto 3 using IHHSubR1, strengthen_sub_decls, sub_tp_notrans_rfn_r, IHHSubR2 |
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
(*assert (wf_env E) by admit. assert (lc_tp Ta) by admit. assert (lc_tp Tr) by admit.*)
inverts H; splits; auto. 
Qed.

Lemma notrans_is_sound : forall E T1 T2, wf_env E -> lc_tp T1 -> lc_tp T2 -> E |= T1 ~<! T2 -> exists q, E |= T1 ~<: T2 @ q.
Proof. Admitted.
 (* TODO: deal with regularity 
introv HWf HLc1 HLc2 H. induction H; eauto try solve [destruct IHsub_tp_notrans; eexists; eauto | destruct IHsub_tp_notrans1; destruct IHsub_tp_notrans2; eexists; eauto].
*)




eexists. eapply sub_tp_notrans_tpsel_lower; eauto.

  Let P2_ (E : env) (q : quality) (S T : tp) (H: E |= S ~<: T @ q) := exists q, E |= S ~<! T @ q.
  Let P0_ (E: env) (q: quality) (t: tm) (T: tp) (H: E  |=  t ~: T  @ q) := True.
  Let P1_ (E : env) (q : quality) (T : tp) (DS : decls) (H: E |= T ~< DS @ q) := True.
  Let P3_ (e : env) (q : quality) (d d0 : decl) (H: sub_decl e q d d0) := True.
  Let P4_ (e : env) (t t0 : tm) (H: path_eq e t t0) := True.
  Let P5_ (e : env) (H: wf_env e) := True.
  Let P6_ (e : env) (t : tp) (H: wf_tp e t) := True.
  Let P7_ (e : env) (d : decl) (H: wf_decl e d) := True.
(* only hard case is sub_tp_trans, which is proven above *)
Lemma notrans_is_complete : (forall E q S T, E |= S ~<: T @ q -> exists q, E |= S ~<! T@ q).
Proof.
mutind_typing P0_ P1_ P2_ P3_ P4_ P5_ P6_ P7_; intros. 
eexists; eapply sub_tp_notrans_rfn_elim; eauto. inverts l. eauto.
assert (lc_tp (S ^tp^ p)) by admit. assert (wf_env E) by admit. eauto. 
assert (lc_tp (U ^tp^ p)) by admit. assert (wf_env E) by admit. eauto. 
(* main case: transitivity: *)

admit. (* obsolete: path_eq was moved to typing *)
destruct H. destruct H0. eauto.
destruct H. destruct H0. eauto.
destruct H. destruct H0. eauto.
destruct H. eauto.
assert (lc_tp T) by admit. assert (wf_env E) by admit. eauto. 
destruct H. assert (lc_tp T) by admit. assert (wf_env E) by admit. eauto. 
destruct H. assert (lc_tp T) by admit. assert (wf_env E) by admit. eauto. 
destruct H. assert (lc_tp T) by admit. assert (wf_env E) by admit. eauto. 
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
























(* doesn't work:
  case := "sub_tp_trans" : String.string
  E : env
  q1 : quality
  q2 : quality
  TMid : tp
  T : tp
  n : forall (p : tm) (L : label), TMid <> tp_sel p L
  s : E |= T ~<: TMid @ q1
  H : forall T1 T2 : tp,
      TMid = tp_fun T1 T2 ->
      (exists p L, T = tp_sel p L) \/
      (exists T3 T4, T = tp_and T3 T4) \/
      (exists T3 T4, T = tp_or T3 T4) \/
      (exists TP DS, T = tp_rfn TP DS) \/
      (exists T1' T2',
       T = tp_fun T1' T2' ->
       exists q, E |= T1 ~<: T1' @ q /\ (exists q0, E |= T2' ~<: T2 @ q0))
  T1 : tp
  T2 : tp
  s0 : E |= TMid ~<: tp_fun T1 T2 @ q2
  H0 : forall T3 T4 : tp,
       tp_fun T1 T2 = tp_fun T3 T4 ->
       (exists p L, TMid = tp_sel p L) \/
       (exists T1 T2, TMid = tp_and T1 T2) \/
       (exists T1 T2, TMid = tp_or T1 T2) \/
       (exists TP DS, TMid = tp_rfn TP DS) \/
       (exists T1' T2',
        TMid = tp_fun T1' T2' ->
        exists q, E |= T3 ~<: T1' @ q /\ (exists q0, E |= T2' ~<: T4 @ q0))
  ============================
   exists T1' T2',
   T = tp_fun T1' T2' ->
   exists q, E |= T1 ~<: T1' @ q /\ (exists q0, E |= T2' ~<: T2 @ q0)


Section InvSubFun0.
  Let P0_ (E: env) (q: quality) (t: tm) (T: tp) (H: E  |=  t ~: T  @ q) := True.  Let P3_ (e : env) (q : quality) (d d0 : decl) (H: sub_decl e q d d0) := True.  Let P4_ (e : env) (t t0 : tm) (H: path_eq e t t0) := True.  Let P5_ (e : env) (H: wf_env e) := True. Let P6_ (e : env) (t : tp) (H: wf_tp e t) := True.  Let P7_ (e : env) (d : decl) (H: wf_decl e d) := True.


  Let P1_ (E : env) (q : quality) (T : tp) (DS : decls) (H: E |= T ~< DS @ q) := forall T1 T2, T = tp_fun T1 T2 -> 
    DS = nil.
  Let P2_ (E : env) (q : quality) (S T : tp) (H: E |= S ~<: T @ q) := forall T1 T2, T = tp_fun T1 T2 -> 
    (exists p, exists L, S = tp_sel p L) \/ (exists T1, exists T2, S = tp_and T1 T2) \/ (exists T1, exists T2, S = tp_or T1 T2) \/ (exists TP, exists DS, S = tp_rfn TP DS) \/ 
    (exists T1', exists T2', S = tp_fun T1' T2' -> exists q, E |= T1 ~<: T1' @ q /\ exists q, E |= T2' ~<: T2 @ q ).


Lemma invert_subtyping_fun0 : 
   (forall E q T DS, E |= T ~< DS @ q -> forall T1 T2, T = tp_fun T1 T2 -> 
    DS = nil) /\
   (forall E q S T, E |= S ~<: T @ q ->  forall T1 T2, T = tp_fun T1 T2 -> 
    (exists p, exists L, S = tp_sel p L) \/ (exists T1, exists T2, S = tp_and T1 T2) \/ (exists T1, exists T2, S = tp_or T1 T2) \/ (exists TP, exists DS, S = tp_rfn TP DS) \/ 
    (exists T1', exists T2', S = tp_fun T1' T2' -> exists q, E |= T1 ~<: T1' @ q /\ exists q, E |= T2' ~<: T2 @ q )).
Proof. 
mutind_typing P0_ P1_ P2_ P3_ P4_ P5_ P6_ P7_; intros; try solve [inverts H;eauto | inverts H0;eauto | inverts H1;eauto | eauto ].

 subst.  admit.
 right. right. right. left. eauto.
 subst. right. right. right. right.

End InvSubFun0.

*)

(*
Lemma invert_subtyping_and_l : forall E T1 T2 T q, E |= tp_and T1 T2 ~<: T @ q -> 
  (exists q, E |= T1 ~<: T @ q) /\ (exists q, E |= T2 ~<: T @ q).
Proof. Admitted.

  mutind_typing P0_ P1_ P2_ P3_ P4_ P5_ P6_ P7_; intros; try solve [ eauto ].

Lemma invert_subtyping_fun: forall E S T U S' T' q1 q2 s,  E |== s ->
  E |= (tp_fun S T) ~<: U @ q1 -> E |= U ~<: (tp_fun S' T') @ q2 -> (~ has_tp_sel U) ->
  exists q1, sub_tp E q1 S' S /\ exists q2, sub_tp E q2 T T'.
Proof. introv. intros HStoTp HSubL. generalize dependent S'. generalize dependent T'. generalize dependent q2.
  dependent induction HSubL; introv; intros HSubR. (* first get all subgoals to shape  S -> T <: S' -> T' *)

    destruct T0; unfold open_tp in *; simpl in *; inverts x. intros. admit. (* peq *)
    admit. (* tp_fun does not expand*)
    intros. set (H2 p L) as HH. unfold not in HH. tauto. (* trans for tp_sel *)
    intros. assert (tp_fun S T = tp_fun S T); auto. set (@IHHSubL1 S T HStoTp H1 (q2 & q0) T'0 S' (sub_tp_trans H0 HSubL2 HSubR)). auto. (* ok trans: use IH *)
    intros. admit. (* refl *)
    intros. admit. (* fun -> do common thing, then use trans*)
    intros. destruct (invert_subtyping_and_l HSubR) as [HSub1 HSub2]. inverts HSub1. apply IHHSubL1 with (q2 := x); auto. admit. admit. admit. 
*)


(*
Inductive subsumes_top : env -> tp -> Prop := 
 | st_top : forall E,  subsumes_top E tp_top
 | st_rfn : forall E T, subsumes_top E T -> subsumes_top E (tp_rfn T nil)
 | st_and : forall E T1 T2, subsumes_top E T1 -> subsumes_top E T2 -> subsumes_top E (tp_and T1 T2)
 | st_or1 : forall E T1 T2, subsumes_top E T1 -> subsumes_top E (tp_or T1 T2)
 | st_or2 : forall E T1 T2, subsumes_top E T2 -> subsumes_top E (tp_or T1 T2).

Hint Constructors subsumes_top.

(*
 | st_sel_punt : forall E p L q,
  E |= tp_top ~<: (tp_sel p L) @ q ->
  subsumes_top E (tp_sel p L).
 | st_sel_lower : forall E p T' q1 DS q2 L S U,
  E |= p ~: T' @ q1 ->
  E |= T' ~< DS @ q2 ->
  lbl.binds L (decl_tp S U) DS ->
  path_safe E p ->
  subsumes_top E (S ^tp^ p) ->
  subsumes_top E (tp_sel p L)
 | st_sel_upper : forall E p T' q1 DS q2 L S U,
  E |= p ~: T' @ q1 ->
  E |= T' ~< DS @ q2 ->
  lbl.binds L (decl_tp S U) DS ->
  path p ->
  subsumes_top E (tp_sel p L) ->
  subsumes_top E (U ^tp^ p).*)

Lemma opening_pres_subsumes_top : forall E T p p', path_eq E p p' -> subsumes_top E (T ^tp^ p) -> subsumes_top E (T ^tp^ p'). 
Proof.
  introv. intros Hpeq H. unfold open_tp in *; simpl. induction T; try solve [inverts H; simpl; auto].
    simpl in *. inverts H. eapply st_sel; eauto.
    induction l. simpl. auto. inverts H2.
Qed.

Lemma and_decls_nil_2 : forall ds, and_decls nil nil ds -> ds = nil.
Proof. introv. intros.   unfold and_decls in H. destruct H as [_ [HDSOk1 [HDSOk2 H]]]. unfold iff in H. assert (forall (l : label) (d : decl),
      lbl.binds l d ds ->
      (exists d1 d2,
       lbl.binds l d1 nil /\
       lbl.binds l d2 nil /\ and_decl d1 d2 d) \/
      lbl.binds l d nil \/ lbl.binds l d nil) by apply H. clear H.
   induction ds; auto. destruct a. unfold lbl.binds in H0. destruct (H0 l d); simpl; auto.
   destruct H. destruct H. destruct H. destruct H. 
   destruct H. destruct H. destruct H. 
Qed.

Lemma or_decls_nil_2 : forall ds1 ds2 ds, or_decls ds1 ds2 ds -> ds1 = nil \/ ds2 = nil -> ds = nil.
Proof. Admitted.

Section InvSubTop.
  Let P0_ (E: env) (q: quality) (t: tm) (T: tp) (H: E  |=  t ~: T  @ q) := True.
  Let P1_ (E : env) (q : quality) (T : tp) (DS : decls) (H: E |= T ~< DS @ q) := subsumes_top E T -> DS = nil.
  Let P2_ (E : env) (q : quality) (T T' : tp) (H: E |= T ~<: T' @ q) := subsumes_top E T -> subsumes_top E T'.
  Let P3_ (e : env) (q : quality) (d d0 : decl) (H: sub_decl e q d d0) := True.
  Let P4_ (e : env) (t t0 : tm) (H: path_eq e t t0) := True.
  Let P5_ (e : env) (H: wf_env e) := True.
  Let P6_ (e : env) (t : tp) (H: wf_tp e t) := True.
  Let P7_ (e : env) (d : decl) (H: wf_decl e d) := True.

Lemma invert_subtyping_top : 
   (forall E q T DS, E |= T ~< DS @ q -> E |= T ~<^ T' -> subsumes_top E T -> DS = nil) /\
   (forall E q T T', E |= T ~<: T' @ q -> subsumes_top E T -> subsumes_top E T').
Proof. 
mutind_typing P0_ P1_ P2_ P3_ P4_ P5_ P6_ P7_; intros; try solve [inverts H;eauto | inverts H0;eauto | inverts H1;eauto | eauto ].

(*cases: *)
    (* expands_rfn *) inverts H0. assert (DSP = nil) by auto. subst. apply and_decls_nil_2; assumption.
    (* expands_and *) inverts H1. assert (DS1 = nil) by auto; assert (DS2 = nil) by auto. subst. apply and_decls_nil_2; assumption.
    (* expands_or *) assert (DS1 = nil \/ DS2 = nil) by (inverts H1; [left; auto | right; auto]). apply or_decls_nil_2 with (ds1 := DS1) (ds2 := DS2); assumption.
    (* sub_tp_rfn_intro *) assert (DS = nil) by auto. subst. inverts H0; auto. 
    (* sub_tp_rfn *) eauto. assert (DS2 = nil). inverts H. unfold LabelSetImpl.Subset in s. simpl in s. induction DS2; auto. destruct a. assert (LabelSetImpl.In l LabelSetImpl.empty). apply (s l). eapply (lbl.binds_In); eauto. LabelSetDecide.fsetdec. subst. inverts H. auto.
    (* sub_tp_rfn_precise *) inverts H0; auto.
      assert (DS2 = nil). unfold LabelSetImpl.Subset in e. simpl in e. induction DS2; auto. destruct a. simpl in e. unfold LabelSetImpl.Equal in e. unfold iff in e. destruct (e l) as [HF _]. assert ( LabelSetImpl.In l LabelSetImpl.empty). LabelSetDecide.fsetdec. rewrite (LabelSetFacts.empty_iff) in H0. contradiction H0. subst. auto.
    (* sub_tp_tpsel_lower *) 
    (* sub_tp_tpsel_upper *) 
    (* sub_tp_path_eq *) apply opening_pres_subsumes_top with (p := p'); auto.
Qed.
End InvSubTop.

assert (E |= (S ^tp^ p) ~<: (tp_sel p L) @ subsumed) by (eapply sub_tp_tpsel_lower; eauto). assert (exists q, E |= tp_top ~<: (S ^tp^ p) @ q) as HSubS by admit. destruct HSubS. eapply st_sel_punt. eapply sub_tp_trans; eauto.
assert (E |= (tp_sel p L) ~<: (U ^tp^ p) @ (q1 & q2)) by (eapply sub_tp_tpsel_upper; eauto). inverts H1 as HSubS. eapply st_sel_punt. eapply sub_tp_trans; eauto.
*)



(*
Reserved Notation "E |= T1 ~<^ T2" (at level 69).

(* chase type member selections up *)
Inductive promote : env -> tp -> tp -> Prop :=
  | promote_upper : forall E p T' DS L S U T,
      E |= p ~: T' @ precise -> E |= T' ~< DS @ precise -> lbl.binds L (decl_tp S U) DS -> (*      path p -> for regularity *)
      E |= (U ^tp^ p) ~<^ T ->
      E |= (tp_sel p L) ~<^ T 
  | promote_lower : forall E p T' DS L S U T,
      E |= p ~: T' @ precise -> E |= T' ~< DS @ precise -> lbl.binds L (decl_tp S U) DS -> (*      path p -> for regularity *)
      E |= (U ^tp^ p) ~<^ T ->
      E |= (S ^tp^ p) ~<^ T
  | promote_refl : forall E T,
      (forall p L, T <> (tp_sel p L)) ->
      E |= T ~<^ T 
      
where "E |= T1 ~<^ T2" := (promote E T1 T2).

  Let P1_ (E : env) (q : quality) (T : tp) (DS : decls) (H: E |= T ~< DS @ q) := True. (*exists T1, exists T2, is_fun T T1 T2 -> DS = nil.*)
  Let P2_ (E : env) (q : quality) (T T' : tp) (H: E |= T ~<: T' @ q) := 
      (exists p, exists L,   T' = tp_sel p L   -> forall U,     E |= T' ~<^ U -> E |= T ~<^ U) /\
      (exists S2, exists T2, T' = tp_fun S2 T2 -> forall S1 T1,                  E |= T ~<^ tp_fun S1 T1 -> exists q1, exists q2, E |= S2 ~<: S1 @ q1 /\ E |= T1 ~<: T2 @ q2).

  mutind_typing P0_ P1_ P2_ P3_ P4_ P5_ P6_ P7_; intros; split; try solve [ repeat eexists; discriminate ].
  repeat eexists. intros. rewrite -> H0 in *.
Show 5.
*)

(*
Lemma and_decls_nil : forall ds1 ds2, and_decls ds1 ds2 nil -> ds1 = nil /\ ds2 = nil.
Proof. introv. intros. 
  unfold and_decls in H. destruct H as [_ [HDSOk1 [HDSOk2 H]]]. assert (forall (l : label) (d : decl), (
      (exists d1 d2, lbl.binds l d1 ds1 /\ lbl.binds l d2 ds2 /\ and_decl d1 d2 d) \/
       lbl.binds l d ds1 \/ 
       lbl.binds l d ds2) -> lbl.binds l d nil). unfold iff in H. apply H.  clear H.  
        unfold lbl.binds in H0. simpl in H0. induction ds1; induction ds2; auto; destruct a. 
         destruct (H0 l d). right. right. simpl. left. auto.
         destruct (H0 l d). right. left. simpl. left. auto.
         destruct (H0 l d). right. left. simpl. left. auto.
Qed.


(*Lemma top_insensitive_opening : forall T p, subsumes_top T -> subsumes_top (T ^tp^ p). 
Proof.
  intros. induction H; auto; unfold open_tp in *; simpl; auto.
Qed.*)

(*Instance EqDec_eq_label : EqDec_eq label.
Proof. unfold EqDec_eq. decide equality; decide equality; eauto. Defined.

Set Implicit Arguments.
Lemma binds_map_3 : forall A B (x: label) (b: B) (f: A -> B) E,
  (forall a b, f a = f b -> a = b) ->
  lbl.uniq E ->
  lbl.binds x b (lbl.map f E) ->
  exists a, lbl.binds x a E /\ b = f a.
Proof.
  labelmap induction E; intros HFInjection HUniq HBTail.
    inversion HBTail. set (lbl.binds_map_1 B A f x b HBTail).
set (lbl.binds_app_uniq_1 B x b _ _ HUniq HBTail).
    unfold lbl.binds in *. simpl in *. destruct (x == x0); subst.
      inverts HUniq. exists a. split. left; auto. inverts HBTail; eauto. inverts H; auto.
      right. auto.
Qed.*)

Inductive not_lambda : tm -> Prop :=
| not_lambda_bvar : forall x, not_lambda (bvar x)
| not_lambda_fvar : forall x, not_lambda (fvar x)
| not_lambda_ref  : forall x, not_lambda (ref x)
| not_lambda_app  : forall x y, not_lambda (app x y)
| not_lambda_new  : forall x y z, not_lambda (new x y z)
| not_lambda_sel  : forall x y, not_lambda (sel x y).
Hint Constructors not_lambda.

(* the hard case is T = tp_rfn TP DS -- need to appeal to a more powerful lemma that says that expansion is monotone under subtyping *)  
Lemma lambdas_dont_have_members: forall E t T q1 DS q2,  E |= t ~: T @ q1 -> E |= T ~< DS @ q2 -> DS <> nil -> not_lambda t.
Proof. 
  introv HT HX HNotNil. generalize dependent q1. generalize dependent t. 
  induction HX; intros; 
    try (inverts HT; eapply (IHHX _ _ _ (typing_sub _ H)); eauto); 
    try tauto. 
  
  destruct t; auto.

*)

(* false: does not work when e.l -> e'.l -- the IH says e' may still be a lambda 
Lemma path_red_path_or_lambda: forall s t t' s', path t -> s |~ t ~~> t' ~| s' -> path t' \/ (exists T, exists tb, t' = lam T tb).
Proof.
  intros. induction H0; inverts H; eauto. inverts H2; auto. right; eauto. set (IHred H2) as IH. left.
*)

(*
Lemma invert_typing_sel : forall E S t U q, E |= sel t l ~: T @ q -> exists q0, exists q1, exists T, E |= lam S t ~: (tp_fun S T) @ q0 /\ sub_tp E q1 (tp_fun S T) U.
Admitted.
*)
(*
Lemma and_decls_nil: and_decls nil nil nil.
Proof. Admitted.

Lemma and_decls_nil_1: forall DS, and_decls nil DS DS.
Proof. Admitted.

Lemma and_decls_nil_2: forall DS, and_decls DS nil DS.
Proof. Admitted.

Lemma or_decls_nil: or_decls nil nil nil.
Proof. Admitted.

Lemma or_decls_nil_1: forall DS, or_decls nil DS nil.
Proof. Admitted.

Lemma or_decls_nil_2: forall DS, or_decls DS nil nil.
Proof. Admitted.

Lemma invert_and_decls_nil_1: forall DS DS', and_decls nil DS DS' -> DS = DS'.
Proof. Admitted.
Lemma invert_and_decls_nil_2: forall DS DS', and_decls DS nil DS' -> DS = DS'.
Proof. Admitted. 

Hint Rewrite invert_and_decls_nil_1 invert_and_decls_nil_2 : decls.
*)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "../metalib") ***
*** End: ***
*)  