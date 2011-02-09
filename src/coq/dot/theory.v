Set Implicit Arguments.
Require Import List.
Require Import Metatheory support syntax_binding.

Reserved Notation "E |= t ~< T @ q" (at level 69).
Reserved Notation "E |= t ~: T @ q" (at level 69).
Reserved Notation "E |= t <: T @ q" (at level 69).

Inductive typing : env -> quality -> tm -> tp -> Prop :=
   | typing_var : forall E x T,
      wf_env E ->
      lc_tp T -> (* for typing_regular *)
      binds x (env_tp T) E ->
      E |= (fvar x) ~: T @ precise

   | typing_sel : forall E q t l T,
      mem E q t (decl_tm l T) ->  
      E |= (sel t l) ~: T @ q

(* it could be simpler to  disallow chaining of subsumption by requiring a precise typing judgement;
   chained subsumption would be replaced by transitivity in the subtyping judgement
   however, member selection might need subsumed typing in order for expansion to be derivable *)
   | typing_sub : forall E q1 q2 t S T,
      E |= t ~: S @ q1->
      sub_tp E q2 S T ->
      E |= t ~: T @ q1 & q2

(* only needed for preservation: rewrite paths in case for CTX-Sel
   could factor this out to subtyping and introduce into typing by subsumption, but prefer to keep subtyping simple *)
   | typing_path_eq : forall E q t T p p', (* precise subtyping is like type equality *) 
      E |= t ~: (T ^tp^ p) @ q ->
      path_eq E p p' ->
      E |= t ~: (T ^tp^ p') @ q

(* the quality of the argument type does not contribute to the quality of the typing of the application, 
   in fact, typing of applications is entirely irrelevant since applications cannot occur in paths *)
   | typing_app : forall E q q' tf Ta Tr ta,
      E |= tf ~: (tp_fun Ta Tr) @ q ->
      E |= ta ~: Ta @ q' ->
      E |= (app tf ta) ~: Tr @ q

(* this judgement may bind a variable to an illegal type (in the environment) 
   However, a lambda with an illegal type for its argument cannot be applied, and the illegal type is confined to its body *)
   | typing_lam : forall L E q S t T,
      (forall x, x \notin L -> (x ~ (env_tp S) ++ E) |= (t ^^ x) ~: T @ q) -> (* x notin FV(T) follows from the stronger x \notin L forall L *)
      wf_tp E (tp_fun S T) ->
      E |= (lam S t) ~: (tp_fun S T) @ q

(* here, variables are bound to potentially illegal types while checking their legality, 
   when the legality is established, the variable is put in the context to type the scope of the let-binding

   T ok (legal) means the lowerbounds of all of T's type members are subtypes of their corresponding upperbounds
    
   T ok doesn't really guarantuee anything about T's value members since they may be initalised to a lambda bound variable
   nonetheless, value members either point to 
     - objects of type T' (T' ok), 
     - lambda's (irrelevant since cannot occur in paths), 
     - or variables (lambda-bound or self): 
        - for lambda-bound vars, we induct: a chain of function applications can only end if the argument is an object (or a lambda, which, again, is irrelevant)
        - self variables are assumed to have the type that's checked in this judgement, or a supertype, but T ok implies T' ok for T <: T'

   during preservation T ok holds for all bindings x : T in the environment, which precludes funny business in transitivity
   the environment only contains object references (for which store typing contains derivations that their types are OK) and path equalities
*)
   | typing_new : forall L E q Tc args t T ds,
      wf_tp E Tc ->
      concrete Tc ->
      expands E precise Tc ds ->
      (forall x, x \notin L -> 
        wf_args_decls (x ~ (env_tp Tc) ++ E) (ds ^ds^ x) args /\
        (x ~ (env_tp(*_ok*) Tc) ++ E) |= (t ^^ x) ~: T @ q) -> (* TODO: indicate that T ok holds for x : T -- needed? or is store typing enough *)
      E |= (new Tc args t) ~: T @ q


where "E |= t ~: T @ q" := (typing E q t T)

with path_eq : env -> tm -> tm -> Prop :=
   | peq_refl : forall E p, (* TODO: only needed if proof of preservation depends on it *)
      path_eq E p p

   | peq_symm : forall E p q, (* TODO: only needed if proof of preservation depends on it *)
      path_eq E p q ->
      path_eq E q p

   | peq_env : forall E a a' l,
      wf_env E ->
      binds a (env_peq (a', l)) E ->
      path_eq E (ref a) (sel a' l)

   | peq_sel : forall E p p' l T q,
      path_eq E p p' ->
      E |= (sel p l) ~: T @ q ->
      path_eq E (sel p l) (sel p' l)

(* check that lowerbounds are subtypes of upperbounds, arguments are values and they have the type declared in the decls, all value labels in decls must have corresponding arg*)
with wf_args_decls : env -> decls -> args -> Prop := 
  | wf_args_decls_tp : forall E q Tl Tu ds args l,
      sub_tp E q Tl Tu ->
      wf_args_decls E ds args ->
      wf_args_decls E ((decl_tp l Tl Tu) :: ds) args
  | wf_args_decls_tm : forall E q l v args args_rest T ds, 
      drop_tm l v args args_rest ->
      value v ->
      E |= v ~: T @ q ->
      wf_args_decls E ds args_rest ->
      wf_args_decls E ((decl_tm l T) :: ds) args
  | wf_args_decls_nil : forall E,
      wf_args_decls E nil nil

with mem : env -> quality -> tm -> decl -> Prop :=
  | mem_ : forall E q1 q2 p T D DS Dopen,
      E |= p ~: T @ q1 ->
      expands E q2 T DS ->
      In D DS ->
      open_decl_cond D p Dopen ->
      mem E (q1 & q2) p Dopen

with expands : env -> quality -> tp -> decls -> Prop := 
  | expands_rfn : forall E q TP DSP DS DSM,
      expands E q TP DSP ->
      and_decls DSP DS DSM ->
      expands E q (tp_rfn TP DS) DSM
  | expands_and : forall E q1 q2 T1 DS1 T2 DS2 DSM,
      expands E q1 T1 DS1 ->
      expands E q2 T2 DS2 ->
      and_decls DS1 DS2 DSM ->
      expands E (q1 & q2) (tp_and T1 T2) DSM
  | expands_or : forall E q1 q2 T1 DS1 T2 DS2 DSM,
      expands E q1 T1 DS1 ->
      expands E q2 T2 DS2 ->
      or_decls DS1 DS2 DSM ->
      expands E (q1 & q2) (tp_or T1 T2) DSM
  | expands_top : forall E,
      expands E precise tp_top nil
  | expands_sub : forall E q1 q2 T U DS,
      sub_tp  E q1 T U ->
      expands E q2 U DS ->
      expands E (q1 & q2) T DS
where "E |= T ~< D @ q" := (expands E q T D)

with sub_tp : env -> quality -> tp -> tp -> Prop :=  (* w/o transitivity*)
  | sub_tp_rfn_intro : forall E q T DS,
      expands E q T DS -> 
      sub_tp E q T (tp_rfn T DS)

  | sub_tp_rfn_sub : forall L E q T DS1 DS2,
      (forall z, z \notin L -> sub_decls (z ~ (env_tp T) ++ E) q (DS1 ^ds^ z) (DS2 ^ds^ z)) ->
      sub_tp E q (tp_rfn T DS1) (tp_rfn T DS2)

  | sub_tp_tpsel_lower : forall E q p L S U,
      mem E q p (decl_tp L S U) ->  (* no need to further subsume bounds: membership may use subsumption which may use sub_tp_rfn_r *)
      sub_tp E subsumed S (tp_sel p L) (* path p follows from implicit requirement that only well-formed types are compared by subtyping *)
(* TODO: is it sound to have `sub_tp E q S (tp_sel p L)` ?? *)

  | sub_tp_tpsel_upper : forall E q p L S U,
      mem E q p (decl_tp L S U) ->  (* no need to further subsume bounds: membership may use subsumption which may use sub_tp_rfn_r *)
      sub_tp E q (tp_sel p L) U (* path p follows from implicit requirement that only well-formed types are compared by subtyping *)

(* below --> not interesting: reflexivity (precise!), function types, intersection, union, top and bottom *)
  | sub_tp_refl : forall E T,
      sub_tp E precise T T
  | sub_tp_trans : forall E q1 q2 T1 T2 T3,
      sub_tp E q1 T1 T2 ->
      sub_tp E q2 T2 T3 ->
      sub_tp E (q1 & q2) T1 T3
  | sub_tp_fun : forall E q1 q2 S1 S2 T1 T2,
      sub_tp E q1 S2 S1 ->
      sub_tp E q2 T1 T2 ->
      sub_tp E (q1 & q2) (tp_fun S1 T1) (tp_fun S2 T2) 
  | sub_tp_and_r : forall E q1 q2 T T1 T2,
      sub_tp E q1 T T1 ->
      sub_tp E q2 T T2 ->
      sub_tp E (q1 & q2) T (tp_and T1 T2)
  | sub_tp_and_l1 : forall E q T T1 T2,
      sub_tp E q T1 T ->
      sub_tp E subsumed (tp_and T1 T2) T
  | sub_tp_and_l2 : forall E q T T1 T2,
      sub_tp E q T2 T ->
      sub_tp E subsumed (tp_and T1 T2) T
  | sub_tp_or_l : forall E q1 q2 T T1 T2,
      sub_tp E q1 T T1 ->
      sub_tp E q2 T T2 ->
      sub_tp E (q1 & q2) (tp_or T1 T2) T
  | sub_tp_or_r1 : forall E q T T1 T2,
      sub_tp E q T T1 ->
      sub_tp E subsumed T (tp_or T1 T2) 
  | sub_tp_or_r2 : forall E q T T1 T2,
      sub_tp E q T T2 ->
      sub_tp E subsumed T (tp_or T1 T2) 
  | sub_tp_top : forall E T,
      sub_tp E subsumed T tp_top
  | sub_tp_bot : forall E T,
      sub_tp E subsumed tp_bot T

where "E |= T1 <: T2 @ q" := (sub_tp E q T1 T2)

with sub_decl : env -> quality -> decl -> decl -> Prop :=
  | sub_decl_tp : forall E q1 q2 l S1 T1 S2 T2,
(*     sub_tp E S1 T1 ->  -- subsumed by well-formedness assumption? *)
     sub_tp E q1 S2 S1 ->
     sub_tp E q2 T1 T2 ->
     sub_decl E (q1 & q2) (decl_tp l S1 T1) (decl_tp l S2 T2) 
  | sub_decl_tm : forall E q l T1 T2,
     sub_tp E q T1 T2 ->
     sub_decl E q (decl_tm l T1) (decl_tm l T2) 

with sub_decls : env -> quality -> decls -> decls -> Prop :=
  | sub_decls_precise : forall E DS1 DS2,
      List.Forall (fun d2 => List.Exists (fun d1 => sub_decl E precise d1 d2) DS1) DS2 ->
      List.Forall (fun d1 => List.Exists (fun d2 => same_label d1 d2) DS2) DS1 ->
      sub_decls E precise DS1 DS2
  | sub_decls_subsumed : forall E DS1 DS2,
      List.Forall (fun d2 => List.Exists (fun d1 => exists q, sub_decl E q d1 d2) DS1) DS2 ->
      sub_decls E subsumed DS1 DS2

with wf_env : env -> Prop := 
  | wf_env_nil : wf_env nil
  | wf_env_cons : forall E x U,
     wf_env E ->
     x \notin dom E -> 
     (forall x, x \notin dom E -> x \notin fv_tp U) -> 
     wf_env (x ~ (env_tp U) ++ E) (* TODO env_tp_new*)

(* TODO: prove wf_tp E T implies lc_tp T  *)
with wf_tp : env -> tp -> Prop :=
  | wf_rfn : forall E T DS,
      wf_tp E T ->
      (forall z, z `notin` dom E -> 
          List.Forall (wf_decl (z ~ (env_tp (tp_rfn T DS)) ++ E)) (DS ^ds^ z)) ->
      wf_tp E (tp_rfn T DS)
  | wf_lam : forall E T1 T2,
      wf_tp E T1 -> 
      wf_tp E T2 ->
      wf_tp E (tp_fun T1 T2)
  | wf_tsel : forall E q p L S U,
      path p ->
      mem E q p (decl_tp L S U) ->
      wf_tp E S -> 
      wf_tp E U ->
      wf_tp E (tp_sel p L)
  | wf_tsel_cls : forall E q p L U,
      path p ->
      mem E q p (decl_tp L tp_bot U) ->
      wf_tp E (tp_sel p L)
  | wf_and : forall E T1 T2,
      wf_tp E T1 -> 
      wf_tp E T2 ->
      wf_tp E (tp_and T1 T2)
  | wf_or : forall E T1 T2,
      wf_tp E T1 -> 
      wf_tp E T2 ->
      wf_tp E (tp_or T1 T2)
  | wf_bot : forall E, wf_tp E tp_bot
  | wf_top : forall E, wf_tp E tp_top
with wf_decl : env -> decl -> Prop :=
  | wf_decl_tp : forall E L S U,
     wf_tp E S ->
     wf_tp E U ->
     wf_decl E (decl_tp L S U)
  | wf_decl_tm : forall E l T,
     wf_tp E T ->
     wf_decl E (decl_tm l T).




(* TODO: store and store typing, reduction
Inductive store_typing

Reserved Notation "a | s ~=> b | s'" (at level 67).


Inductive red : store -> tm -> store -> tm -> Prop :=

where "a | s ~=> b | s'" := (red s a s' b).

Definition preservation := forall E q t t' T,
  E |= t ~: T  @ q->
  t ~=> t' ->
  E |= t' ~: T @ q.

Definition progress := forall t T q, 
  nil |= t ~: T @ q ->
     value t 
  \/ exists t', t ~=> t'.
*)
  


(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "../metalib") ***
*** End: ***
*)  