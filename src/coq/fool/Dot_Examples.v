(** The DOT calculus -- Examples *)

Require Export Dot_Labels.
Require Import Metatheory LibTactics_sf.
Require Export Dot_Syntax Dot_Definitions Dot_Rules Dot_Lemmas.

Section Ex.

Hint Constructors wf_store wf_env red lc_tm lc_tp lc_decl lc_args lc_decls_lst value.
Hint Constructors vars_ok_tp valid_label.
Hint Constructors typing expands sub_tp sub_decl wf_tp wf_decl wfe_tp.
Hint Unfold decls_ok decls_uniq.

Tactic Notation
  "pick" "fresh" ident(atom_name) "and" ident(atom_name')
  "excluding" constr(L) "and" constr(L')
  "and" "apply" constr(H)
  :=
    first [apply (@H L L') | eapply (@H L L')];
      match goal with
        | |- forall _, _ `notin` _ -> _ =>
          let Fr := fresh "Fr" in intros atom_name Fr
        | |- forall _, _ `notin` _ -> _ =>
          fail 1 "because" atom_name "is already defined"
        | _ =>
          idtac
      end.

Tactic Notation
  "pick" "fresh" ident(atom_name) "and" ident(atom_name')
  "and" "apply" constr(H)
  :=
    let L := gather_atoms in
    let L := beautify_fset L in
    let L' := gather_atoms in
    let L' := beautify_fset L' in
    pick fresh atom_name and atom_name' excluding L and L' and apply H.

Ltac crush_rules :=
  repeat (match goal with
(*          | [ |- ?S |~ app (lam ?T ?B) ?V ~~> ?R ~| ?S ] => apply red_beta*)
(*          | [ |- ?E |= (lam ?T ?B) ~: _ ] => let x := fresh "x" in pick fresh x and apply typing_abs*)
            | [ |- ?E |= (new ?X ?Tc ?args) ~: _ ] => let x := fresh "x" in let y := fresh "y" in pick fresh x and y and apply typing_new
            | [ |- ?E |= (fvar ?X) ~: _ ] => apply typing_var
            | [ |- wf_tp ?E (tp_rfn _ _) ] => let x:= fresh "x" in pick fresh x and apply wf_rfn
            | [ |- wf_env ((?X, ?T) :: ?R) ] => rewrite_env ([(X,T)] ++ R); apply wf_env_cons
(*          | [ |- lc_tm (lam ?T ?B) ] => let x := fresh "x" in pick fresh x and apply lc_lam*)
            | [ |- lc_tm (new ?Tc ?A ?B) ] => let x:= fresh "x" in pick fresh x and apply lc_new
            | [ |- lc_tp (tp_rfn _ _) ] =>  let x:= fresh "x" in pick fresh x and apply lc_tp_rfn
            | [ |- lc_args ( _ :: _ ) ] => apply lc_args_cons_value
            | [ |- wfe_tp _ tp_top ] => apply wfe_top
            | [ |- wfe_tp _ tp_bot ] => apply wfe_bot
(*          | [ |- wfe_tp _ (tp_fun _ _) ] => apply wfe_fun*)
            | [ |- _ |= _ ~<: tp_top ] => apply sub_tp_top
            | [ |- context[(?Y ^ ?X)] ] => unfold open; unfold open_rec_tm; simpl
            | [ |- context[(?Y ^^ ?X)] ] => unfold open; unfold open_rec_tm; simpl
            | [ |- context[(?Y ^ds^ ?X)] ] => unfold open_decls; simpl
            | [ |- context[(?Y ^dsl^ ?X)] ] => unfold open_decls_lst; simpl
(*          | [ |- value (lam ?T ?B) ] => apply value_lam *)
            | [ |- context[decls_binds _ _ _] ] => let H:=fresh "H" in introv H; inversion H
            | [ |- context[lbl.binds _ _ _] ] => let H:=fresh "H" in introv H; inversion H
            | [ |- context[ctx_bind _ _ _] ] => unfold ctx_bind; simpl
            | [ H: (?L, _) = (?L', _) |- _ ] => inversion H; subst; simpl; split
            | [ H: False |- _ ] => inversion H
            | [ H: decls_fin ?DSL1 = ?DSL2 \/ decls_inf ?DSL1 = ?DSL2 |- _ ] => inversions H
            | [ H: decls_fin ?DSL1 = decls_fin ?DSL2 |- _ ] => inversions H
            | [ H: decls_fin ?DSL1 = decls_inf ?DSL2 |- _ ] => inversions H
            | [ H: decls_inf ?DSL1 = decls_fin ?DSL2 |- _ ] => inversions H
            | [ H: decls_inf ?DSL1 = decls_inf ?DSL2 |- _ ] => inversions H
            | [ H: lbl.binds _ _ _ |- _ ] => inversions H
            | [ |- decls_uniq _ ] => unfold decls_uniq; intros
            | [ |- _ /\ _ ] => split
            | [ |- _ ] => simpl; eauto
          end).

Parameter l : label.
Axiom l_value_label : value_label l.
Hint Resolve l_value_label.

Parameter Lt : label.
Axiom Lt_type_label : type_label Lt.
Hint Resolve Lt_type_label.

(*
Definition ex1 := app (lam tp_top 0) (lam tp_top 0).
Example ex1_red : nil |~ ex1 ~~> (lam tp_top 0) ~| nil.
Proof. unfold ex1. crush_rules. Qed.
*)

Definition ex2 := new tp_top nil 0.
Example ex2_red : exists a, nil |~ ex2 ~~> 0 ^^ (fvar a) ~| ((a ~ (tp_top, nil)) ++ nil).
Proof.
  unfold ex2. pick fresh a. exists a. apply red_new; crush_rules.
Qed.

Definition ex3 := new (tp_rfn tp_top [(l, decl_tm tp_top)]) [(l, bvar 0)] (sel 0 l).
Example ex3_red : exists a, exists store', nil |~ ex3 ~~> (sel 0 l) ^^ (fvar a) ~| store'.
Proof.
  unfold ex3. pick fresh a. exists a. eexists. apply red_new; crush_rules; try inversion H0; subst;
  left; crush_rules.
Qed.

(*
Definition ex4 := new (tp_rfn tp_top [(l, decl_tm tp_top)]) [(l, lam tp_top 0)] (sel 0 l).
Example ex4_red : exists a, exists store', nil |~ ex4 ~~> (sel 0 l) ^^ (ref a) ~| store'.
Proof.
  unfold ex4. pick fresh a. exists a. eexists. apply red_new; crush_rules.
Qed.
*)

(*
Example ex_id_typ : (nil,nil) |= (lam tp_top 0) ~: (tp_fun tp_top tp_top).
Proof. crush_rules. Qed.
*)

(*
Example ex1_typ : (nil,nil) |= ex1 ~: tp_top.
Proof.
  unfold ex1. apply typing_app with (S:=tp_top) (T':=tp_fun tp_top tp_top); crush_rules.
Qed.
*)

Example ex2_typ : nil |= ex2 ~: tp_top.
Proof. unfold ex2. crush_rules. Qed.

(*
Example cast_typ : (nil,nil) |= (lam tp_bot (app (lam tp_top 0) (lam (tp_sel 0 Lt) 0))) ~: tp_fun tp_bot tp_top.
Proof.
  crush_rules.
  apply typing_app with (S:=tp_top) (T':=(tp_fun (tp_sel x Lt) (tp_sel x Lt))); simpl; crush_rules.
  Lemma wfe_sel_bot_mem : forall L x, x `notin` L ->
    ((x, tp_bot) :: nil, nil) |= x ~mem~ Lt ~: decl_tp tp_top tp_bot.
  Proof.
    introv H.
    replace (decl_tp tp_top tp_bot) with ((decl_tp tp_top tp_bot) ^d^ x).
    apply mem_path with (T:=tp_bot) (DS:=decls_inf nil); crush_rules.
    apply expands_bot_inf_nil; crush_rules.
    apply decls_binds_inf with (dsl:=nil). reflexivity. intros F. inversion F. left. auto. crush_rules.
  Qed.
  Lemma wfe_sel_bot : forall L x, x `notin` L -> wfe_tp ((x, tp_bot) :: nil, nil) (tp_sel x Lt).
    introv H.
    apply wfe_any with (DT:=decls_inf nil); crush_rules.
    apply wf_tsel_1 with (S:=tp_top) (U:=tp_bot); crush_rules.
    apply wfe_sel_bot_mem with (L:=L); assumption.
    apply expands_tsel with (S:=tp_top) (U:=tp_bot); crush_rules.
    apply wfe_sel_bot_mem with (L:=L); assumption.
    apply expands_bot_inf_nil; crush_rules.
  Qed.
  apply wfe_sel_bot with (L:=empty) (x:=x); assumption.
  apply vars_ok_tp_sel. eapply vars_ok_var. crush_rules.
  apply wfe_sel_bot with (L:=empty) (x:=x); assumption.
  apply wfe_sel_bot with (L:=empty) (x:=x); assumption.
Qed.
*)
End Ex.
