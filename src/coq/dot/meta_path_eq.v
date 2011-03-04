Set Implicit Arguments.
Require Import List.
Require Import syntax_binding theory.
Require Import Metatheory LibTactics_sf support.
Require Import meta_pres_subst meta_weakening meta_inversion meta_binding meta_regular meta_decls meta_quality.
Require Import Coq.Program.Equality.


Lemma red_pres_path: forall s t t' s' E T q DS q', 
  E |== s' -> path t -> s |~ t ~~> t' ~| s' -> (E, s') |= t' ~: T @ q -> (E, s') |= T ~< DS @ q' -> DS <> nil
    -> path t'.
Proof.
  introv HStoTp Hpath Hred Htp HX. generalize dependent q'. generalize dependent q. generalize dependent T. generalize dependent DS. induction Hred; intros; inverts Hpath; eauto. inverts H2 (*value v*); auto.

  destruct (invert_typing_lam HStoTp Htp) as [? [? [? [? [? [? [? HSubFun]]]]]]]. 
  set (expands_sub_safe HStoTp HSubFun HX) as HXF. destruct HXF as [qq HXF']. set (invert_expands_fun HXF'). tauto.
  apply path_sel. 

  destruct (invert_typing_sel HStoTp Htp) as [T' [q1 [HT [DS' [q2 [HX' [D [HIn [S [Hopen [q3 HSub]]]]]]]]]]].
  eapply IHHred; eauto. unfold not. intros. induction DS'; eauto. inversion H0.
Qed.

Lemma red_implies_peq: forall E s t t' s', E |== s' -> s |~ t ~~> t' ~| s' -> path t -> path t' -> path_eq (E, s') t t'. 
Proof. Admitted.
