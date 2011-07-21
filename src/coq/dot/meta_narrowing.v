Set Implicit Arguments.
Require Import List.
Require Import syntax_binding theory theory_alg.
Require Import Metatheory LibTactics_sf support meta_regular meta_binding meta_weakening.
Require Import Coq.Program.Equality.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Logic.Decidable.


Lemma path_from_path_eq : forall E p p', path_eq E p p' -> path p /\ path p'.
Proof. intros. Hint Constructors path. dependent induction H; jauto. Qed.

Lemma path_from_path_safe : forall E p, path_safe E p -> path p.
Proof. intros. Hint Constructors path. dependent induction H; auto. Qed.
Hint Resolve path_from_path_safe.

Hint Extern 1 (path ?p) =>
  match goal with
  | H: path (sel p ?l) |- _ => inversion H
  | H: path_eq _ p _ |- _ => apply (proj1 (path_from_path_eq H)); auto
  | H: path_eq _ _ p |- _ => apply (proj2 (path_from_path_eq H)); auto
  end.


(* E, z : Tz, F on paper is reversed in the mechanisation, since new bindings are prepended*)
Definition splice_env (E: ctx) z F (s: store) Tz := (F ++ [(z, (Tz, (precise, true)))] ++ E, s).

Instance EqDec_eq_atom `(@EqDec atom eq eq_equivalence) : EqDec_eq atom.
Proof. trivial. Defined.

Lemma uniq_from_wf_env : forall E s, wf_env (E, s) -> uniq E.
Proof. 
intros.
dependent induction H; eauto.
Qed.
Hint Resolve uniq_from_wf_env.

(* internal: specialize hypotheses with satisfiable embedded equalities, drop the (SEEMINGLY) unsatisfiable ones *)
Ltac sphyps :=
  repeat match goal with H: ?T |- _ => 
    match T with
    | context [?a = _]  => 
      match type of a with
        | ?x => try (let h := fresh in lets h: H (@eq_refl x); generalizes h); clear H
      end
    | path ?p -> _  =>  (* can't just try to strip any old hypothesis, too wild! *)
       try (let h := fresh in let Hp := fresh in assert (path p) as Hp by eauto; lets h: H Hp; generalizes h); clear H
    | _ => generalizes H
    end
  end.

(* use this tactic (with care, since it may drop valid hypotheses) to 
     - instantiate the equalities that arise from dependent induction, 
     - destruct conjunctions, ... *)
Ltac simplhyps :=  jauto_set_hyps; intros; sphyps; intros; jauto_set_hyps; intros.
Ltac simplhyps_except H :=  jauto_set_hyps; intros; generalize H; sphyps; intros; jauto_set_hyps; intros.

(* the resulting quality is precise iff the q' for each member was precise, otherwise subsumed
  intuitively, collect all the qualities for the individual members, find the minimum, and presto!
  now, how to convince coq? *)
Lemma sub_decls_from_exists_sub_decl : forall L E T DS1 DS2,
 (forall z : atom, z `notin` L ->
    forall (l : label) (d1 d2 : decl),
    lbl.binds l d2 (DS2 ^ds^ z) ->
    lbl.binds l d1 (DS1 ^ds^ z) ->
    exists q', sub_decl (ctx_bind E z T) q' d1 d2)
 -> exists q, 
   (forall z, z \notin L -> forall_decls (ctx_bind E z T) (DS1 ^ds^ z) (DS2 ^ds^ z) (fun E => fun d1 => fun d2 => sub_decl E q d1 d2)).
Proof. 
  intros. pick fresh z for L. specialize (H z Fr).
  (* try to construct H's other premises, so we can get to the goodies *)
(*    
  Lemma forall_decls_nil_1 : forall E q DS,
   forall_decls E nil DS  (fun (E0 : env) (d1 d2 : decl) => sub_decl E0 q d1 d2).
  Proof. 
  Lemma forall_decls_nil_2 : forall E q DS,
   forall_decls E DS nil (fun (E0 : env) (d1 d2 : decl) => sub_decl E0 q d1 d2).
  Proof. 
  Hint Resolve forall_decls_nil_1 forall_decls_nil_2.
  induction DS1; induction DS2; try solve [simpl in *; eauto | idtac]. 

  destruct a. destruct a0. simpl_env in *.
  forwards : H ; eauto.*)

Admitted. (* TODO: meh, should be a mere technical Coq hurdle -- obviously true, right? what could possibly go wrong *)


Section VarsOk.
  Hint Unfold ctx_bind.
  Hint Constructors vars_ok_tp vars_ok_decl vars_ok_tm vars_ok_decls vars_ok_args.

  Let P (e : env) (t : tp)   (v : vars_ok_tp e t)     := forall X bi E s bi' F, e = ((F ++ X ~ bi ++ E), s) -> vars_ok_tp ((F ++ X ~ bi' ++ E), s) t.
  Let P0 (e : env) (d : decl) (v : vars_ok_decl e d)  := forall X bi E s bi' F, e = ((F ++ X ~ bi ++ E), s) -> vars_ok_decl ((F ++ X ~ bi' ++ E), s) d.
  Let P1 (e : env) (t : tm)   (v : vars_ok_tm e t)    := forall X bi E s bi' F, e = ((F ++ X ~ bi ++ E), s) -> vars_ok_tm ((F ++ X ~ bi' ++ E), s) t.
  Let P2 (e : env) (d : decls)(v : vars_ok_decls e d) := forall X bi E s bi' F, e = ((F ++ X ~ bi ++ E), s) -> vars_ok_decls ((F ++ X ~ bi' ++ E), s) d.
  Let P3 (e : env) (a : args) (v : vars_ok_args e a)  := forall X bi E s bi' F, e = ((F ++ X ~ bi ++ E), s) -> vars_ok_args ((F ++ X ~ bi' ++ E), s) a.
  Lemma vars_ok_narrowing : 
   (forall (e : env) (t : tp)   (v : vars_ok_tp e t),   @P  e t v) /\
   (forall (e : env) (d : decl) (v : vars_ok_decl e d), @P0 e d v) /\
   (forall (e : env) (t : tm)   (v : vars_ok_tm e t),   @P1 e t v) /\
   (forall (e : env) (d : decls)(v : vars_ok_decls e d),@P2 e d v) /\
   (forall (e : env) (a : args) (v : vars_ok_args e a), @P3 e a v).
  Proof with simpl_env; eauto.
    apply vars_ok_mutind; intros; unfold P, P0, P1, P2, P3 in *; subst; clear P P0 P1 P2 P3; eauto; intros; subst.

    simplhyps; eapply vars_ok_tp_rfn; eauto; intros x Fr; unfold ctx_bind in *; simpl in *; 
      eapply H1 with (F0 := ((x, (t, (precise, true))) :: F)); simpl; eauto.

    injsubst H; analyze_binds b...
    injsubst H; analyze_binds b...

    simplhyps; eapply vars_ok_lam; eauto; intros x Fr; unfold ctx_bind in *; simpl in *; 
      eapply H1 with (F0 := ((x, (t, (precise, true))) :: F)); simpl; eauto.

    eapply vars_ok_new; eauto; intros x Fr; unfold ctx_bind in *; simpl in *; [
      eapply H0 with (F0 := ((x, (t, (precise, true))) :: F)) |
      eapply H1 with (F0 := ((x, (t, (precise, true))) :: F)) ]; simpl; eauto.
  Qed.
End VarsOk.

Lemma narrowing_vars_ok_tp : forall X bi E s bi' F T, vars_ok_tp ((F ++ X ~ bi ++ E), s) T -> vars_ok_tp ((F ++ X ~ bi' ++ E), s) T. 
Proof. intros. destructs vars_ok_narrowing. eapply H0; eauto. Qed.

Lemma narrowing_path_safe : forall F z T q T' q' E s p,
 path_safe (F ++ z ~ (T, (q, true)) ++ E, s) p -> path_safe (F ++ z ~ (T', (q', true)) ++ E, s) p.
Proof. intros. 
  Hint Constructors path_safe. 
  dependent induction H; eauto.  
   intros. 
    destruct (x == z). 
      (* x === z *) destruct e. 
        analyze_binds H; eapply path_safe_fvar; eauto.

      (* x =/= z *) unfold equiv, complement in *.
        analyze_binds H; eauto.
Qed.

Section Q.
Lemma quality_subsumption : forall E t T q, E |= t ~: T @ precise -> E |= t ~: T @ q.
Proof.  Hint Resolve sub_tp_refl.
intros. replace q with (precise & q). eapply typing_sub; eauto. induction q; unfold qconj; simpl; eauto. Qed.
End Q.

Section NarrowingTyping.
  Hint Constructors sub_decl sub_qual path_eq wf_env wf_tp wf_decl.
  Hint Resolve typing_var typing_ref typing_sel typing_peq typing_app typing_lam typing_new expands_rfn expands_and expands_or expands_top expands_bot 
sub_tp_rfn sub_tp_rfn_elim sub_tp_tpsel_lower sub_tp_tpsel_upper sub_tp_refl sub_tp_top sub_tp_bot sub_tp_fun sub_tp_and_r sub_tp_or_l sub_tp_and_l1 sub_tp_and_l2 sub_tp_or_r1 sub_tp_or_r2. (* typing/expands/subtyping minus transitivity-like rules *)
  Hint Resolve narrowing_vars_ok_tp narrowing_path_safe.

  Let Ptyp (E: ctx) (s: store) (Sz Tz: tp) (Ez : env) (q: quality) (t: tm) (T: tp) (H: Ez |=  t ~: T  @ q) :=  forall F z,
    Ez = splice_env E z F s Tz -> path t -> exists q, (splice_env E z F s Sz) |= t ~: T @ q. 
  Let Pexp (E: ctx) (s: store) (Sz Tz: tp) (Ez : env) (q : quality) (T : tp) (DS : decls) (H: Ez |= T ~< DS @ q) := forall F z,
    Ez = splice_env E z F s Tz -> exists q, (splice_env E z F s Sz) |= T ~< DS @ q.
  Let Psub (E: ctx) (s: store) (Sz Tz: tp) (Ez : env) (q : quality) (T1 T2 : tp) (H: Ez |= T1 ~<: T2 @ q) := forall F z,
    Ez = splice_env E z F s Tz -> exists q, (splice_env E z F s Sz) |= T1 ~<: T2 @ q.
  Let Psbd (E: ctx) (s: store) (Sz Tz: tp) (Ez : env) (q : quality) (d1 d2 : decl) (H: sub_decl Ez q d1 d2) :=  forall F z ,
    Ez = splice_env E z F s Tz -> exists q, sub_decl (splice_env E z F s Sz) q d1 d2.
  Let Ppeq (E: ctx) (s: store) (Sz Tz: tp) (Ez : env) (t1 t2 : tm) (H: path_eq Ez t1 t2) :=  forall F z , 
    Ez = splice_env E z F s Tz -> path_eq (splice_env E z F s Sz) t1 t2.
  Let Pwfe (E: ctx) (s: store) (Sz Tz: tp) (Ez : env) (H: wf_env Ez) :=  forall F z , 
    Ez = splice_env E z F s Tz -> wf_env (splice_env E z F s Sz).
  Let Pwft (E: ctx) (s: store) (Sz Tz: tp) (Ez : env) (T : tp) (H: wf_tp Ez T) :=  forall F z , 
    Ez = splice_env E z F s Tz -> wf_tp (splice_env E z F s Sz) T.
  Let Pwfd (E: ctx) (s: store) (Sz Tz: tp) (Ez : env) (d : decl) (H: wf_decl Ez d) :=  forall F z , 
    Ez = splice_env E z F s Tz -> wf_decl (splice_env E z F s Sz) d.


Lemma sub_narrowing_typing : forall E s Sz Tz qz,
  (E, s) |= Sz ~<: Tz @ qz ->
 ((forall Ez q t T (H: Ez |= t ~: T @ q), (@Ptyp E s Sz Tz Ez q t T H)) /\ 
  (forall Ez q T DS (H: Ez |= T ~< DS @ q), (@Pexp E s Sz Tz Ez q T DS H)) /\ 
  (forall Ez q T T' (H: Ez |= T ~<: T' @ q), (@Psub E s Sz Tz Ez q T T' H))  /\ 
  (forall (Ez : env) (q : quality) (d d0 : decl) (H : sub_decl Ez q d d0), (@Psbd E s Sz Tz Ez q d d0 H)) /\  
  (forall (Ez : env) (t t0 : tm) (H : path_eq Ez t t0), (@Ppeq E s Sz Tz Ez t t0 H)) /\  
  (forall (Ez : env) (H : wf_env Ez), (@Pwfe E s Sz Tz Ez H)) /\
  (forall (Ez : env) (t : tp) (H : wf_tp Ez t), (@Pwft E s Sz Tz Ez t H)) /\  
  (forall (Ez : env) (d : decl) (H : wf_decl Ez d), (@Pwfd E s Sz Tz Ez d H))).
Proof. 
  introv HSubZ.
  mutind_typing  (@Ptyp E s Sz Tz) (@Pexp E s Sz Tz) (@Psub E s Sz Tz) (@Psbd E s Sz Tz) (@Ppeq E s Sz Tz) (@Pwfe E s Sz Tz) (@Pwft E s Sz Tz) (@Pwfd E s Sz Tz);  unfold Ptyp, Pexp, Psub, Psbd, Ppeq, Pwfe, Pwft, Pwfd in *; clear Ptyp Pexp Psub Psbd Ppeq Pwfe Pwft Pwfd; unfold splice_env in *; intros; subst;
    try solve [ auto 
              | inversion H; subst; symmetry in H1; contradiction (app_cons_not_nil _ (z, (Tz, (precise, true))) F E H1) (* wf_env_nil *)
              | exists precise; eauto (* sub_tp_refl *)
(* eauto messes up on the previous two cases, so they must be handled separately -- see below *)
              | eauto 
              | injsubst H0; eauto
              | match goal with H: ?T |- _ =>  match T with
                 | path ?p  => try solve [inversion H | idtac] end end
              | simplhyps; eauto
              | simplhyps; simplhyps; try solve [ eauto
                  | eexists; eapply typing_sub with (S := S); eauto
                  | eexists; eapply expands_sub with (U := U); eauto
                  | eexists; eapply sub_tp_trans with (TMid := TMid); eauto]]. 

  (* typing_var *)
    injsubst H0.
    destruct (x == z). 
      (* x === z *) destruct e. 
        (* recover that Tz = T from binding in hypothesis b *)
        analyze_binds_uniq b; eauto; injsubst BindsTacVal.

        (* first construct precise typing for x : Sz *)
        forwards Hprecise : typing_var (F ++ [(x, (Sz, (precise, true)))] ++ E) s x Sz precise; eauto. 
          simpl in H. eapply H; eauto.  (* wf_env *)

        eexists; eapply typing_sub; eauto. 
          eapply weakening_subtyping; eauto; simpl; simpl_alist; fsetdec.

      (* x =/= z *) unfold equiv, complement in *.
        eexists; eapply typing_var; eauto. 
          analyze_binds_uniq b; eauto.

  (* sub_tp_rfn *) 
  simplhyps_except a; simplhyps_except a. rename x into qtp. rename x0 into qx. 
  
Lemma narrow_sub_decls_from_narrow_sub_decl_pt1 : forall L DS1 DS2 F z Tz E s T Sz,
 (forall z0 : atom,
       z0 `notin` L ->
       forall (l : label) (d1 d2 : decl),
       lbl.binds l d2 (DS2 ^ds^ z0) ->
       lbl.binds l d1 (DS1 ^ds^ z0) ->
       forall (F0 : list (atom * (tp * (quality * bool)))) (z1 : atom),
       ctx_bind (F ++ [(z, (Tz, (precise, true)))] ++ E, s) z0 T = (F0 ++ [(z1, (Tz, (precise, true)))] ++ E, s) ->
       exists q,
       sub_decl (F0 ++ [(z1, (Sz, (precise, true)))] ++ E, s) q d1 d2)
 ->
 (forall z0 : atom,
       z0 `notin` L ->
       forall (l : label) (d1 d2 : decl),
       lbl.binds l d2 (DS2 ^ds^ z0) ->
       lbl.binds l d1 (DS1 ^ds^ z0) ->
       exists q,
       sub_decl (ctx_bind (F ++ [(z, (Sz, (precise, true)))] ++ E, s) z0 T) q d1 d2).
Proof. intros.
  forwards : H; eauto; [ 
    unfold ctx_bind; simpl; f_equal; instantiate (1 := z); instantiate (1 := ((z0, (T, (precise, true))) :: F)); trivial
    | eapply H3].
Qed.
 
set (@narrow_sub_decls_from_narrow_sub_decl_pt1 L DS1 DS2 F z Tz E s T Sz H2) as Hds0.
remember ((F ++ [(z, (Sz, (precise, true)))] ++ E, s)) as Eds in Hds0.
replace ((F ++ [(z, (Sz, (precise, true)))] ++ E, s)) with Eds in *.


  destruct (@sub_decls_from_exists_sub_decl L _ _ DS1 DS2 Hds0) as [qds Hds].

Lemma  narrow_sub_decls_from_narrow_sub_decl_pt2 : forall L E T DS1 DS2 q q',
   (forall z, z \notin L -> forall_decls (ctx_bind E z T) (DS1 ^ds^ z) (DS2 ^ds^ z) (fun E => fun d1 => fun d2 => sub_decl E q d1 d2))
->
   (forall z, z \notin L -> forall_decls (ctx_bind E z T) (DS1 ^ds^ z) (DS2 ^ds^ z) (fun E => fun d1 => fun d2 => sub_decl E (q & q') d1 d2)).
Proof.
  intros. unfold forall_decls in *; intros. forwards : H; eauto. induction q; induction q'; unfold qconj in *; simpl in *; induction H3; eauto.
Qed.

  set (@narrow_sub_decls_from_narrow_sub_decl_pt2 L Eds T DS1 DS2 qds (q & (qtp & qx)) Hds) as Hsubds.
  eexists; eapply sub_tp_rfn; eauto; intros; induction q; induction qds; induction qtp; induction qx; split; forwards [Hdom Hq] : a; auto.


  (* sub_tp_tpsel_lower *) (* Ltac just drives me MAD -- why is this case not covered by simplhyps; simplhyps? good luck finding out *)
    forwards [qtp Htp]: H; eauto. forwards [qx Hx]: H0; auto. eexists; eauto.

  (*  wf_env_cons *)
  induction F; inverts H0; simpl_env in *; eauto.
  
  (* wf_tp_rfn *)
  eapply wf_rfn; eauto; intros x Fr l d' Hin; unfold ctx_bind in *; simpl in *; 
    eapply (H0 x Fr l d' Hin ((x, (tp_rfn T DS, (precise, true))) :: F)); simpl; eauto.

(* at some point Coq was sore: "Error: Attempt to save a proof with existential variables still non-instantiated" even though there are no subgoals left because eauto discharges goals while leaving existentials uninstantiated in certain cases

diagnosed using Show Proof.  -- relevant excerpts:
  (let case := "sub_tp_refl" in
          fun (E0 : env) (T : tp) (q : quality)
            (F : list (atom * (tp * (quality * bool)))) 
            (z : atom) (_ : E0 = (F ++ [(z, (Tz, (precise, true)))] ++ E, s)) =>
          ex_intro
            (fun q0 : quality =>
             (F ++ [(z, (Sz, (precise, true)))] ++ E, s) |= T ~<: T @ q0)
            ?28778
            (sub_tp_refl (F ++ [(z, (Sz, (precise, true)))] ++ E, s) T ?28778))
  (let case := "wf_env_nil" in
          fun (P : store) (F : list (atom * (tp * (quality * bool))))
            (z : atom)
            (H : (nil, P) = (F ++ [(z, (Tz, (precise, true)))] ++ E, s)) =>
          ?35 E s Sz Tz qz HSubZ P F z H)
*)
Qed.
End NarrowingTyping.