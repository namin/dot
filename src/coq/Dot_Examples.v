(** The DOT calculus -- Examples *)

Require Export Dot_Labels.
Require Import Metatheory LibTactics_sf.
Require Export Dot_Syntax Dot_Definitions Dot_Rules.

Section Ex.

Hint Constructors wf_store red lc_tm lc_tp lc_decl lc_args lc_decls value.

Ltac crush_red :=
  repeat (match goal with
            | [ |- ?S |~ app (lam ?T ?B) ?V ~~> ?R ~| ?S ] => apply red_beta
            | [ |- lc_tm (lam ?T ?B) ] => let x := fresh in pick fresh x and apply lc_lam
            | [ |- lc_tm (new ?Tc ?A ?B) ] => let x:= fresh in pick fresh x and apply lc_new
            | [ |- lc_tp (tp_rfn _ _) ] =>  let x:= fresh in pick fresh x and apply lc_tp_rfn
            | [ |- lc_args ( _ :: _ ) ] => apply lc_args_cons
            | [ |- context[(?Y ^ ?X)] ] => unfold open; unfold open_rec_tm; simpl
            | [ |- context[(?Y ^^ ?X)] ] => unfold open; unfold open_rec_tm; simpl
            | [ |- context[(?Y ^ds^ ?X)] ] => unfold open_decls; simpl
            | [ |- value (lam ?T ?B) ] => apply value_lam
            | [ |- context[lbl.binds _ _ _] ] => let H:=fresh in introv H; inversion H
            | [ H: (?L, ?V) = (?L', ?V') |- _ ] => inversion H; subst; simpl; split
            | [ H: False |- _ ] => inversion H
            | [ |- _ /\ _ ] => split
            | [ |- _ ] => auto
          end).

Parameter l : label.
Axiom l_value_label : value_label l.
Hint Resolve l_value_label.

Definition ex1 := app (lam tp_top 0) (lam tp_top 0).
Example ex1_red : nil |~ ex1 ~~> (lam tp_top 0) ~| nil.
Proof. unfold ex1. crush_red. Qed.

Definition ex2 := new tp_top nil 0.
Example ex2_red : exists a, nil |~ ex2 ~~> 0 ^^ (ref a) ~| ((a ~ (tp_top, nil)) ++ nil).
Proof.
  unfold ex2. pick fresh a. exists a. apply red_new; crush_red.
Qed.

Definition ex3 := new (tp_rfn tp_top [(l, decl_tm tp_top)]) [(l, bvar 0)] (sel 0 l).
Example ex3_red : exists a, exists store', nil |~ ex3 ~~> (sel 0 l) ^^ (ref a) ~| store'.
Proof.
  unfold ex3. pick fresh a. exists a. eexists. apply red_new; crush_red.
Qed.

Definition ex4 := new (tp_rfn tp_top [(l, decl_tm tp_top)]) [(l, lam tp_top 0)] (sel 0 l).
Example ex4_red : exists a, exists store', nil |~ ex4 ~~> (sel 0 l) ^^ (ref a) ~| store'.
Proof.
  unfold ex4. pick fresh a. exists a. eexists. apply red_new; crush_red.
Qed.

End Ex.
