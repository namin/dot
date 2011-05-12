Set Implicit Arguments.
Require Import List.
Require Import syntax_binding theory.
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

(* attempts at inversion lemma for subtyping of function types:

(1) FAILED
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


(2) FAILED
if we exclude type selections as the middleman in our sub_tp_trans (and expands_sub), we can prove the lemma ignoring these annoying types,
but we can't use it in preservation since we can't invert S -> T <: S' <: T' if any of those types contains a type selection...

excluding type selection is contagious: as soon as we exclude it anywhere, need to exclude it in all the cases of is_fun 
(e.g, the sub_tp_fun case requires transitivity for the components of the function type, thus, 
if transitivity excludes type selection as its middlemen, the constituents of the original function type need to exclude type selections as well)


(3) OK?
this seems succesful so far:
have alternate subtyping/expansion relations that don't have transitivity
they also don't track quality, to avoid nested existentials in the induction hypotheses in the proof -- I cannot figure out how to make coq's automation open existentials

prove soundness and completeness wrt the original relations (where expansion has been merged into subtyping so we can induct more easily)

*)

Definition sub_decls E q DS1 DS2 := forall_decls E DS1 DS2 (fun E => fun d1 => fun d2 => sub_decl E q d1 d2).

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
      (forall z, z \notin L -> forall_decls (ctx_bind E z T) (DS1 ^ds^ z) (DS2 ^ds^ z) sub_decl_notrans) ->
      and_decls DSP DS DS1 ->
      lbl.dom DS2 [<l=] lbl.dom DS1 -> (* no longer implied by sub_decls, but that forall/exists construction made induction impractical *)
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

where "E |= T1 ~<! T2" := (sub_tp_notrans E T1 T2)

with sub_decl_notrans : env -> decl -> decl -> Prop :=
  | sub_decl_notrans_tp : forall E S1 T1 S2 T2,
      E |= S2 ~<! S1 ->
      E |= T1 ~<! T2 ->
      sub_decl_notrans E (decl_tp S1 T1) (decl_tp S2 T2) (*(q1 & q2) *)
  | sub_decl_notrans_tm : forall E T1 T2,
      E |= T1 ~<! T2 ->
      sub_decl_notrans E (decl_tm T1) (decl_tm T2).

Scheme sub_tp_notrans_indm   := Induction for sub_tp_notrans Sort Prop
  with sub_decl_notrans_indm := Induction for sub_decl_notrans Sort Prop.

Combined Scheme sub_tp_notrans_mutind from sub_tp_notrans_indm, sub_decl_notrans_indm.



Hint Constructors sub_tp_notrans sub_decl_notrans.

Section Soundness.
  (* TODO: deal with regularity  *)
  Lemma wf_ax : forall E, wf_env E. Proof. Admitted. (* TODO: used in cases for expands_top and expands_bot *)
  Lemma lc_ax : forall T, lc_tp T. Proof. Admitted. (* TODO: used in cases for sub_tp_rfn_elim *) 
  Hint Resolve wf_ax lc_ax.

  Hint Constructors sub_decl sub_qual path_eq wf_env wf_tp wf_decl.
  Hint Resolve sub_tp_rfn sub_tp_rfn_elim sub_tp_tpsel_lower sub_tp_tpsel_upper sub_tp_top sub_tp_bot sub_tp_fun sub_tp_and_r sub_tp_or_l sub_tp_and_l1 sub_tp_and_l2 sub_tp_or_r1 sub_tp_or_r2 theory.expands_rfn theory.expands_and theory.expands_or theory.expands_top theory.expands_bot sub_tp_refl. (*but not transitivity*)

  Lemma and_decls_nil: and_decls nil nil nil.            Proof. Admitted. (* TODO *)
  Lemma and_decls_nil_1: forall DS, and_decls nil DS DS. Proof. Admitted. (* TODO *)
  Lemma and_decls_nil_2: forall DS, and_decls DS nil DS. Proof. Admitted. (* TODO *)
  Lemma or_decls_nil: or_decls nil nil nil.              Proof. Admitted. (* TODO *)
  Lemma or_decls_nil_1: forall DS, or_decls nil DS nil.  Proof. Admitted. (* TODO *)
  Lemma or_decls_nil_2: forall DS, or_decls DS nil nil.  Proof. Admitted. (* TODO *)

  (* TODO: proof will need decls_ok DS from well formedness of the type that expanded to DS for uniqueness of labels, and wf_env for sub_tp_refl *)
  Lemma sub_decls_refl : forall L E T DS,
     forall z : atom,
     z `notin` L ->
     forall_decls (ctx_bind E z T) (DS ^ds^ z) 
       (DS ^ds^ z)
       (fun (E0 : env) (d1 d2 : decl) => sub_decl E0 subsumed d1 d2).
  Proof. Admitted. (* TODO *) (*
    unfold forall_decls. intros. set (DS' := DS ^ds^ z) in *. 
    gen d1 d2.
    decls induction DS'; intros. 
      inversion H1.

      assert (lbl.uniq DS') as HUnique by admit. (* wf_decls *)
      forwards: (lbl.binds_cons_uniq_1 _ _ _ _ _ _ HUnique H0); eauto. forwards: (lbl.binds_cons_uniq_1 _ _ _ _ _ _ HUnique H1); eauto.
      destruct H2 as [[HEq HEq'] | IH']; destruct H3 as [[HEq1 HEq1'] | IH1']; subst; eauto.
      skip. (*refl*)
      eapply IHDS'; eauto.
*)

Lemma sub_decls_sound : forall L E DS1 DS2 T,
  (forall z : atom, z `notin` L -> forall (l : label) (d1 d2 : decl),
   lbl.binds l d2 (DS2 ^ds^ z) -> lbl.binds l d1 (DS1 ^ds^ z) ->
     exists q, sub_decl (ctx_bind E z T) q d1 d2) ->
  (forall z : atom, z `notin` L ->
   forall_decls (ctx_bind E z T) (DS1 ^ds^ z) (DS2 ^ds^ z)
     (fun (E0 : env) (d1 d2 : decl) => sub_decl E0 subsumed d1 d2)).
Proof.
  unfold forall_decls. intros. destruct (H z H0 l d1 d2 H1 H2) as [q Hsub].
  inverts Hsub; [ apply sub_decl_tp with (q1 := q1) (q2 := q2) (q := subsumed); eauto |
    apply sub_decl_tm with (q1 := q1) (q := subsumed); eauto].
Qed.

  Hint Resolve and_decls_nil and_decls_nil_1 and_decls_nil_2 or_decls_nil or_decls_nil_1 or_decls_nil_2 sub_decls_refl sub_decls_sound.

  (* specialize hypotheses with satisfiable embedded equalities, drop the unsatisfiable ones *)
  Ltac sphyps :=
    repeat match goal with H: ?T |- _ => 
      match T with
      | forall x, ?a = _ -> _  =>  (* TODO: why does generalized `context [ ?a = _ ] ` version not work? *)
        match type of a with
          | ?x => try (let h := fresh in lets h: H (@eq_refl x); generalizes h); clear H
        end
      | _ => generalizes H
      end
    end.
  Ltac simplhyps :=  jauto_set_hyps; intros; sphyps; intros; jauto_set_hyps; intros.

  (* automate most uses of trans (all except for the trans T one, probably), since we know what its argument should be: for a subgoal that needs to show `exists q, E |= T ~<: tp_sel p L @ q`, the argument is `S` if there is a hypothesis `E |= T ~<! ?S` 
   also, these hints avoid uninstantiated existentials that would arise if we were to let eauto have at it with expands_sub and sub_tp_trans *)
  Hint Extern 2 (exists q, ?E |= ?T ~<: _ @ q) =>
    match goal with
    | H: E |= T ~<! ?S |- _ => eexists; eapply sub_tp_trans with (TMid := S); eauto 3
    end.
  Hint Extern 2 (exists q, ?E |= _ ~<: ?T @ q) =>
    match goal with
    | H: E |= ?S ~<! T |- _ => eexists; eapply sub_tp_trans with (TMid := S); eauto 3
    end.
  Hint Extern 2 (exists q, ?E |= _ ~< ?DS @ q) =>
    match goal with
    | H: E |= ?S ~< DS @ _ |- _ => eexists; eapply expands_sub with (U := S); eauto 3
    end.

  Ltac sub_tp_rfn_top DS := 
    eapply sub_tp_rfn with (DS1 := DS) (DS2 := DS) (q := subsumed); [
      eauto 3 | eauto 3 | pick fresh z and apply sub_decls_refl | fsetdec | intros; discriminate].


  Let P (E : env) (T1 T2 : tp) (H : E |= T1 ~<! T2) := (exists q, E |= T1 ~<: T2 @ q) /\ (forall DS, T2 = tp_rfn tp_top DS -> exists q, E |= T1 ~< DS @ q).
  Let P0 (E : env) (D1 D2 : decl) (H : sub_decl_notrans E D1 D2) := exists q, sub_decl E q D1 D2.
  Lemma notrans_is_sound : (forall (E : env) (T1 T2 : tp) (H : E |= T1 ~<! T2), @P E T1 T2 H) /\
              (forall (E : env) (D1 D2 : decl) (H : sub_decl_notrans E D1 D2), @P0 E D1 D2 H). 
  Proof. unfold P, P0. clear P P0.
    apply sub_tp_notrans_mutind; first [ (split; 
         [ (* subtyping *) simplhyps; try solve [ exists precise; eauto (* to instantiate sub_tp_refl's existential quality *) | eauto 3 | idtac ]
         | (* expansion *) introv HEq; try injsubst HEq; subst; 
             try destructs IHsub_tp_notrans1; try destructs IHsub_tp_notrans2; try destructs IHsub_tp_notrans; 
             simplhyps; try solve [ discriminate | eauto 2 | eexists; eapply expands_sub; eauto 2 | eexists; intros; eauto 3]]) 
         | (* sub_decl *) intros; exists subsumed; simplhyps; eauto 
      ];
      [ eexists; eapply sub_tp_rfn with (L := L) (DS1 := DS1) (DS2 := DS2) (q := subsumed); eauto 3 using expands_sub; intros; discriminate
      | eexists; eapply expands_sub with (U := tp_rfn tp_top DS0); eauto; eapply sub_tp_rfn with (q1 := x & x1); eauto using expands_sub; intros; discriminate
      | eexists; eapply sub_tp_trans with (TMid := tp_and T1 T2); [eauto 2 | sub_tp_rfn_top DSM]
      | eexists; eapply sub_tp_trans with (TMid := tp_or T1 T2); [eauto 2 | sub_tp_rfn_top DSM]
      | eexists; sub_tp_rfn_top (nil : decls); eauto using expands_sub
      | eexists; eapply expands_sub with (U := tp_rfn tp_top DS); eauto].
  Qed. (* 5s *)
End Soundness.
(* Show Existentials is your friend when combatting uninstantiated existentials before Coq will let you Qed *)


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
Proof. Admitted. (* TODO *)


Definition transitivity_on TMid := forall E T T',  E |= T ~<! TMid -> E |= TMid ~<! T' -> E |= T ~<! T'.
Hint Unfold transitivity_on.

Section Narrowing.
  (* specialize hypotheses with satisfiable embedded equalities, drop the unsatisfiable ones *)
  Ltac sphyps :=
    repeat match goal with H: ?T |- _ => 
      match T with
      | context [?a = _]  => 
        match type of a with
          | ?x => try (let h := fresh in lets h: H (@eq_refl x); generalizes h); clear H
        end
      | _ => generalizes H
      end
    end.
  Ltac simplhyps :=  jauto_set_hyps; intros; sphyps; intros; jauto_set_hyps; intros.

  Hint Unfold splice_env.

  Let P (E: ctx) (s: store) (Sz Tz: tp) (Ez : env) (S T : tp) (H : Ez |= S ~<! T) := forall F z, 
    Ez = splice_env E z F s Tz -> (splice_env E z F s Sz) |= S ~<! T.

  Let P0 (E: ctx) (s: store) (Sz Tz: tp) (Ez : env) (D1 D2 : decl) (H : sub_decl_notrans Ez D1 D2) := forall F z,
    Ez = splice_env E z F s Tz -> sub_decl_notrans (splice_env E z F s Sz) D1 D2.

Lemma sub_narrowing_aux : forall s E Sz Tz,
(*  transitivity_on Tz -> *)
  (E, s) |= Sz ~<! Tz ->
    (forall (Ez : env) (T1 T2 : tp) (H : Ez |= T1 ~<! T2), @P E s Sz Tz Ez T1 T2 H) /\
    (forall (Ez : env) (D1 D2 : decl) (H : sub_decl_notrans Ez D1 D2), @P0 E s Sz Tz Ez D1 D2 H).
Proof. 
  unfold P, P0. clear P P0. introv (*HTrans*) HSubZ. 
  destruct (proj1 ((proj1 notrans_is_sound) _ _ _ HSubZ)) as [qsz Hsz].

  apply sub_tp_notrans_mutind; intros; subst; simplhyps; eauto 4.

(*Hint Extern 1 (splice_env ?E ?z ?F ?s ?Sz |= ?p ~: ?T @ ?q) =>
  match goal with
  | H:  splice_env E z F s ?Tz |= p ~: T @ ?q' |- _ => (idtac; match goal with
     | Hsz: (E, s) |= Sz ~<: Tz @ ?qs |- _ => 
         let qn := fresh in let Hn := fresh in
         lets [qn Hn] : ((proj1 (sub_narrowing_typing Hsz)) _ _ _ _ H F z); [auto | eauto 2 | eapply Hn]
    end)
  end.*)
  
  Hint Resolve narrowing_vars_ok_tp narrowing_path_safe.
  forwards [qn Hn] : (proj1 (sub_narrowing_typing Hsz)); eauto 2.
  eapply sub_tp_notrans_tpsel_r; unfold splice_env in *; eauto. 

  eapply sub_tp_notrans_rfn_r; eauto.   
    intros zd Frd.  specialize (H1 zd Frd). 
    unfold forall_decls, ctx_bind, splice_env in *. simpl in *. simpl_env in *.
  intros. forwards : H1; eauto. simpl; f_equal. instantiate (1 := z). instantiate (1 :=  (zd, (T, (precise, true))) :: F). trivial. simpl_env in *. trivial.

  forwards [qn Hn] : (proj1 (sub_narrowing_typing Hsz)); eauto 2.
Qed.
  End Narrowing.
Lemma narrow_sub_decls: forall L E S T DS1 DS2,  
(*  transitivity_on T ->*)
  E |=  S ~<! T ->
  (forall z : atom, z `notin` L ->
     forall_decls (ctx_bind E z T) (DS1 ^ds^ z) (DS2 ^ds^ z) sub_decl_notrans) -> 
  (forall z : atom, z `notin` L ->
     forall_decls (ctx_bind E z S) (DS1 ^ds^ z) (DS2 ^ds^ z) sub_decl_notrans).
Proof. 
  unfold forall_decls. intros. forwards : H0; eauto. unfold ctx_bind in *. destruct E. simpl in *. 
  forwards : (proj2 (sub_narrowing_aux H)); eauto. unfold splice_env; simpl; f_equal. instantiate (1 := z). instantiate (1 := nil). auto. eapply H5.
Qed.

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

(* TODO: the core case... do we need to introduce some kind of sub_tp_notrans rule? as in fsub? *)
rename t into p. rename T into Ta. rename T0 into Tb'. rename T' into Twoele. rename T'0 into T'. rename Twoele into T.
rename DS0 into DS'. rename S0 into S'. rename U0 into U'. rename q0 into q'. rename q1 into q.
clear IHHSubR1 IHHSubR2 IHHSubL1 IHHSubL2.
(*
  H1 : path_safe E p
  H4 : path p

  H0 : E |= p ~: T @ q
  HSubL2 : E |= T ~<! tp_rfn tp_top DS
  H : lbl.binds l (decl_tp S U) DS

  H3 : E |= p ~: T' @ q'
  HSubR2 : E |= T' ~<! tp_rfn tp_top DS'
  H2 : lbl.binds l (decl_tp S' U') DS'

  HSubL1 : E |= Ta ~<! S ^tp^ p
  HSubR1 : E |= U' ^tp^ p ~<! Tb'
  ============================
   E |= Ta ~<! Tb
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
    skip. (* TODO: sub_decls_notrans_refl *) skip.
    eapply sub_tp_notrans_rfn_r with (DS1 := DS1); eauto 2. 
    skip. (* TODO: IH for sub_decls (change from True above to something useful) *)
    apply and_decls_nil_1.
    apply sub_tp_notrans_trans with (TMid := TMid); eauto.
  Qed.

End NoTransSoundComplete.


(* more convenient interface to above *)
Lemma invert_expands_fun: forall E S T DS q,  E |= tp_fun S T ~< DS @ q -> DS = nil.
Proof. Admitted. (* TODO *)


Lemma invert_expands_concrete : forall E s Tc DS q, (E, s) |= Tc ~< DS @ q -> concrete Tc -> 
    exists DS', (E, s) |= Tc ~< DS' @ precise /\ exists q, sub_decls (E, s) q DS' DS.
Proof. Admitted. (* TODO *)


(* XXXX need to strenghten definition of E |= ok *)
Lemma sub_tp_trans_safe : forall E s S TMid T q1 q2, 
  E |== s -> (E, s) |= ok -> (E, s) |= S ~<: TMid @ q1 -> (E, s) |= TMid ~<: T @ q2 -> exists q3, (E, s) |= S ~<: T @ q3.
Proof. Admitted. (* TODO *)  
(*
  intros.  set TMid as TMid'. dependent induction TMid; try solve [exists (q1 & q2); apply sub_tp_trans with (TMid := TMid'); auto; unfold not; intros ? ? HH; inversion HH | idtac]; clear TMid'.   
 
  destruct (regular_subtyping H1) as [HWfEnv [HLcS HLcSel]]. 
*)



Lemma expands_sub_safe : forall E s S TMid DS q1 q2, E |== s -> (E, s) |= S ~<: TMid @ q1 -> (E, s) |= TMid ~< DS @ q2 -> exists q3, (E, s) |= S ~< DS @ q3.
Proof. Admitted. (* TODO *)



Lemma invert_typing_lam : forall E S t U q s, E |== s -> (E, s) |=  ok -> (E, s) |= lam S t ~: U @ q -> 
      exists q1, exists L, exists T, (forall x, x \notin L -> (ctx_bind (E, s) x S) |= (t ^^ x) ~: T @ q1) /\
      wf_tp (E, s) (tp_fun S T) /\ lc_tp T /\
      exists q2, (E, s) |= (tp_fun S T) ~<: U @ q2.
Proof. Admitted. (* TODO *)

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
Proof. Admitted. (* TODO *)


Lemma invert_wf_store_uniq : forall s, wf_store s -> uniq s.
Proof. Admitted. (* TODO *)

Lemma invert_red_store_dom : forall s t t' s', s |~ t ~~> t' ~| s' -> dom s [<=] dom s'.
Proof. Admitted. (* TODO *)


(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "../metalib") ***
*** End: ***
*)  