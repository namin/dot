Set Implicit Arguments.
Require Import List.
Require Import syntax_binding.
Require Import Metatheory support.

Reserved Notation "E |= t ~< T @ q" (at level 69).
Reserved Notation "E |= t ~: T @ q" (at level 69).
Reserved Notation "E |= t ~<: T @ q" (at level 69).
(*Reserved Notation "E |= t ~mem~ D @ q" (at level 69).*)

Inductive has_tp_sel : tp -> Prop :=
 | hts_tp_sel : forall p L, has_tp_sel (tp_sel p L)
 | hts_and1   : forall T T', has_tp_sel T' -> has_tp_sel (tp_and T' T)
 | hts_and2   : forall T T', has_tp_sel T' -> has_tp_sel (tp_and T T')
 | hts_or1   : forall T T', has_tp_sel T' -> has_tp_sel (tp_or T' T)
 | hts_or2   : forall T T', has_tp_sel T' -> has_tp_sel (tp_or T T').

Inductive typing : env -> quality -> tm -> tp -> Prop :=
   | typing_var : forall E x T,
      wf_env E -> lc_tp T -> (* for typing_regular *)
      ctx_binds E x T ->
      E |= (fvar x) ~: T @ precise

   | typing_ref : forall G P a T args, (* this is the only typing rule that peeks into the store, well, the path_eq judgement does as well *)
      wf_env (G, P) -> lc_tp T -> (* for typing_regular *)
      binds a (T, args) P ->
      (G, P) |= (ref a) ~: T @ precise

   | typing_sel : forall E q1 q2 t T' D DS l T,
(*      E |= t ~mem~ (decl_tm l T) @ q ->   *)
      E |= t ~: T' @ q1 -> E |= T' ~< DS @ q2 -> LabelMapImpl.binds l D DS -> open_decl_cond D t (decl_tm T) ->
      E |= (sel t l) ~: T @ q1 & q2

(* it could be simpler to  disallow chaining of subsumption by requiring a precise typing judgement;
   chained subsumption would be replaced by transitivity in the subtyping judgement
   however, member selection might need subsumed typing in order for expansion to be derivable *)
   | typing_sub : forall E q1 q2 t S T,
      E |= t ~:  S @ q1 ->
      E |= S ~<: T @ q2 ->
      E |= t ~: T @ q1 & q2

(* the quality of the argument type does not contribute to the quality of the typing of the application, 
   in fact, typing of applications is entirely irrelevant since applications cannot occur in paths *)
   | typing_app : forall E q q' tf Ta Tr ta,
      E |= tf ~: (tp_fun Ta Tr) @ q ->
      E |= ta ~: Ta @ q' ->
      E |= (app tf ta) ~: Tr @ q

(* this judgement may bind a variable to an illegal type (in the environment) 
   However, a lambda with an illegal type for its argument cannot be applied, and the illegal type is confined to its body *)
   | typing_lam : forall L E q S t T,
      (forall x, x \notin L -> (ctx_bind E x S) |= (t ^^ x) ~: T @ q) -> (* x notin FV(T) follows from the stronger x \notin L forall L *)
      lc_tp T -> (* XXX necessary? *)
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
      E |= Tc ~< ds @ precise ->
(*       decls_ok ds /\  -- implied by expansion of well-formed type *)
      LabelMapImpl.uniq args -> (* ctor args are unique by label *)
      (LabelMapImpl.dom ds) [=l=] (LabelMapImpl.dom args) -> (* all ctor args must have declaration with same label*)
      (forall x, x \notin L -> (forall l d, LabelMapImpl.binds l d ds -> 
        (forall U T, d ^d^ x = decl_tp T U -> (exists q, (ctx_bind E x Tc) |= T ~<: U @ q)) /\ (* for each type member: its lower bound must be a subtype of its upper bound *)
        (forall T, d ^d^ x = decl_tm T -> (exists v,  (* for each term member there's a ctor argument with the same label that provides a well-typed value *)
          LabelMapImpl.binds l v args /\ value (v ^^ x) /\ (exists q, (ctx_bind E x Tc) |= (v ^^ x) ~: T @ q))))) ->
      (forall x, x \notin L -> (ctx_bind E x Tc) |= (t ^^ x) ~: T @ q) ->  (* in principle, x.L would now be a valid middle man in sub_tp_trans since the type members in Tc's expansion have been checked *)
      (* lc_tp T ->  not needed -- implied by typing_regular for the above judgement *)
      E |= (new Tc args t) ~: T @ q

where "E |= t ~: T @ q" := (typing E q t T)

(* inlined to make induction easier 
with mem : env -> quality -> tm -> decl -> Prop :=
  | mem_ : forall E q1 q2 t T D DS Dopen,
      E |= t ~: T @ q1 -> (* requiring a precise judgment makes preservation harder without gaining anything afaict *)
      E |= T ~< DS @ q2 -> In D DS ->
      open_decl_cond D t Dopen ->
      mem E (q1 & q2) t Dopen

where "E |= t ~mem~ D @ q" := (mem E q t D)
 (*exists T, exists q1, exists q2, exists DS, exists D', E |= t ~: T @ q1 /\ E |= T ~< DS @ q2 /\ q = q1 & q2 /\ In D' DS /\ open_decl_cond D' t D*)
*)


with expands : env -> quality -> tp -> decls -> Prop := 
  | expands_sub : forall E q1 q2 T U DS,
      (~ has_tp_sel U) -> (* by the same reasoning as sub_tp_trans, the only valid use of p.L for U is when we have checked S <: T  for L : S..T, so that we might as well directly use p.L's upperbound T for U instead of p.L *) 
      E |= T ~<: U  @ q1 ->
      E |=       U ~< DS @ q2 ->
      E |= T       ~< DS  @ (q1 & q2)

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
(*      wf_env E -> *)
      expands E precise tp_top nil
where "E |= T ~< D @ q" := (expands E q T D)


with sub_tp : env -> quality -> tp -> tp -> Prop :=
  | sub_tp_rfn_intro : forall E q T DS,
      expands E q T DS -> 
      E |= T ~<: (tp_rfn T DS) @ q

  | sub_tp_rfn_elim : forall E T DS, (* not redundant with sub_tp_rfn even though it can derive the empty refinement T{}; T{} and T would be unrelated without sub_tp_rfn_elim*)
(*      wf_env E ->
      lc_tp (tp_rfn T DS) -> *)
      E |= (tp_rfn T DS) ~<: T @ subsumed

  | sub_tp_rfn : forall L E T DS1 DS2,
      LabelMapImpl.dom DS2 [<l=] LabelMapImpl.dom DS1 -> (* subsumption may lose members *)
      (forall z, z \notin L -> (forall l d1 d2, LabelMapImpl.binds l d1 DS1 -> LabelMapImpl.binds l d2 DS2 -> exists q,
        sub_decl (ctx_bind E z T) q (d1 ^d^ z) (d2 ^d^ z)))       ->
      E |= (tp_rfn T DS1) ~<: (tp_rfn T DS2) @ subsumed

  | sub_tp_rfn_precise : forall L E T DS1 DS2,
      LabelMapImpl.dom DS2 [=l=] LabelMapImpl.dom DS1 -> (* we didn't lose any members *)
      (forall z, z \notin L -> (forall l d1 d2, LabelMapImpl.binds l d1 DS1 -> LabelMapImpl.binds l d2 DS2 ->
        sub_decl (ctx_bind E z T) precise (d1 ^d^ z) (d2 ^d^ z))) ->
      E |= (tp_rfn T DS1) ~<: (tp_rfn T DS2) @ precise

  | sub_tp_tpsel_lower : forall E p T' q1 DS q2 L S U,
      E |= p ~: T' @ q1 -> E |= T' ~< DS @ q2 -> LabelMapImpl.binds L (decl_tp S U) DS ->
      E |= (S ^tp^ p) ~<: (tp_sel p L) @ subsumed (* path p follows from implicit requirement that only well-formed types are compared by subtyping *)
            (* subsuming a lower bound to its type member selection loses members irrespective of the membership quality *)

  | sub_tp_tpsel_upper : forall E p T' q1 DS q2 L S U,
      E |= p ~: T' @ q1 -> E |= T' ~< DS @ q2 -> LabelMapImpl.binds L (decl_tp S U) DS ->
      E |= (tp_sel p L) ~<: (U ^tp^ p) @ (q1 & q2) (* path p follows from implicit requirement that only well-formed types are compared by subtyping *)

(* we can't have unfettered transitivity, because that foil typing_new's well-formedness check that all type members have conforming bounds:
   "S <: T because p.L : S..T said so", not because they actually are -- with the current path safety check, p can only cause transitivity after it's been all patted down and shit *)
  | sub_tp_trans : forall E q1 q2 TMid T T',
  (*      (forall p L, TMid = tp_sel p L -> E |= p safe) -> no sneaky middlemen: type members may only be selected on paths that have been checked by typing_new *)
      (~ has_tp_sel TMid) ->  (* slightly stronger condition than necessary for soundness to simplify meta-theory: in principle it's enough to check TMid <> tsel p L, since composite TMid (tsel p L /\ Top) as middlemen implies their constituents were middlemen as well
             unless p is rooted in an object reference that has been checked by typing_new, there's no guarantuee its type members' lowerbounds are a subtypes of the corresponding upperbounds
             if it is safe, can recover the same judgement from the bounds directly without going through the path selection *)
      E |= T ~<: TMid        @  q1      ->
      E |=       TMid ~<: T' @       q2 ->
      E |= T          ~<: T' @ (q1 & q2)

(* only needed for preservation: rewrite paths in case for CTX-Sel -- in subtyping so typing inversion lemma's don't need to account for two different kinds of typing slack: subtyping and path rewriting *)
  | sub_tp_path_eq : forall E T p p', (* precise subtyping is like type equality *) 
    path_eq E p p' ->
    E |= (T ^tp^ p') ~<: (T ^tp^ p) @ precise

(* what follows is standard: reflexivity (precise!), function types, intersection, union, top and bottom *)
  | sub_tp_refl : forall E T, E |= T ~<: T @ precise
  | sub_tp_top  : forall E T, E |= T ~<: tp_top @ subsumed
  | sub_tp_bot  : forall E T, E |= tp_bot ~<: T @ subsumed
  | sub_tp_fun : forall E q1 q2 S1 S2 T1 T2,
      E |= S2 ~<: S1 @ q1 -> E |= T1 ~<: T2 @ q2->
      E |= (tp_fun S1 T1) ~<: (tp_fun S2 T2) @ (q1 & q2)
  | sub_tp_and_r : forall E q1 q2 T T1 T2,
      E |= T ~<: T1 @ q1 -> E |= T ~<: T2 @ q2->
      E |= T ~<: (tp_and T1 T2) @ (q1 & q2)
  | sub_tp_or_l : forall E q1 q2 T T1 T2,
      E |= T1 ~<: T @ q1 -> E |= T2 ~<: T @ q2->
      E |= (tp_or T1 T2) ~<: T @ (q1 & q2)
  | sub_tp_and_l1 : forall E q T T1 T2,
      E |= T1 ~<: T @ q ->
      E |= (tp_and T1 T2) ~<: T @ subsumed
  | sub_tp_and_l2 : forall E q T T1 T2,
      E |= T2 ~<: T @ q ->
      E |= (tp_and T1 T2) ~<: T @ subsumed
  | sub_tp_or_r1 : forall E q T T1 T2,
      E |= T ~<: T1 @ q ->
      E |= T ~<: (tp_or T1 T2) @ subsumed
  | sub_tp_or_r2 : forall E q T T1 T2,
      E |= T ~<: T2 @ q ->
      E |= T ~<: (tp_or T1 T2) @ subsumed

where "E |= T1 ~<: T2 @ q" := (sub_tp E q T1 T2)

with sub_decl : env -> quality -> decl -> decl -> Prop :=
  | sub_decl_tp : forall E q1 q2 S1 T1 S2 T2,
(*     sub_tp E S1 T1 ->  -- subsumed by well-formedness assumption *)
     sub_tp E q1 S2 S1 ->
     sub_tp E q2 T1 T2 ->
     sub_decl E (q1 & q2) (decl_tp S1 T1) (decl_tp S2 T2) 
  | sub_decl_tm : forall E q T1 T2,
     sub_tp E q T1 T2 ->
     sub_decl E q (decl_tm T1) (decl_tm T2) 

(* path equality is needed for preservation because evaluation changes types that cannot be related otherwise *)
with path_eq : env -> tm -> tm -> Prop :=
   | peq_refl : forall E p, (* TODO: only needed if proof of preservation depends on it *)
      path_eq E p p

   | peq_symm : forall E p q, (* used in invert_subtyping_fun *)
      path_eq E p q ->
      path_eq E q p

   | peq_env : forall G P a Tc args l a',
      wf_env (G, P) ->
      binds a (Tc, args) P ->
      LabelMapImpl.binds l (ref a') args ->
      path_eq (G, P) (ref a') (sel a l)

   | peq_sel : forall E p p' l T q,
      path_eq E p p' ->
      E |= (sel p l) ~: T @ q ->
      path_eq E (sel p l) (sel p' l)

with wf_env : env -> Prop := 
  | wf_env_nil : forall P, wf_env (nil, P)
  | wf_env_cons : forall E x U P,
     wf_env (E, P) ->
     x `notin` dom E -> 
     (forall x, x `notin` dom E -> x `notin` fv_tp U)-> 
     wf_env ((x ~ U ++ E), P)

(* TODO: prove wf_tp E T implies lc_tp T  *)
with wf_tp : env -> tp -> Prop :=
  | wf_rfn : forall L E T DS,
      decls_ok DS -> (* no dups or invalid label/decl combos *)
      wf_tp E T ->
      (forall z, z `notin` L ->
          forall l d, LabelMapImpl.binds l d DS -> (wf_decl (ctx_bind E z (tp_rfn T DS)) (d ^d^ z))) ->
      wf_tp E (tp_rfn T DS)
  | wf_lam : forall E T1 T2,
      wf_tp E T1 -> 
      wf_tp E T2 ->
      wf_tp E (tp_fun T1 T2)
  | wf_tsel : forall E q1 q2 T' DS p L S U,
      path p ->
(*      E |= p ~mem~ (decl_tp L S U) @ q -> *)
      E |= p ~: T' @ q1 -> E |= T' ~< DS @ q2 -> LabelMapImpl.binds L (decl_tp S U) DS ->
      wf_tp E (S ^tp^ p) -> 
      wf_tp E (U ^tp^ p) ->
      wf_tp E (tp_sel p L)
  | wf_tsel_cls : forall E q1 q2 T' DS p L U,
      path p ->
(*      E |= p ~mem~ (decl_tp L tp_bot U) @ q -> *)
      E |= p ~: T' @ q1 -> E |= T' ~< DS @ q2 -> LabelMapImpl.binds L (decl_tp tp_bot U) DS ->
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
  | wf_decl_tp : forall E S U,
     wf_tp E S ->
     wf_tp E U ->
     wf_decl E (decl_tp S U)
  | wf_decl_tm : forall E T,
     wf_tp E T ->
     wf_decl E (decl_tm T).

Scheme typing_indm         := Induction for typing Sort Prop 
  with expands_indm        := Induction for expands Sort Prop
  with sub_tp_indm         := Induction for sub_tp Sort Prop
  with sub_decl_indm       := Induction for sub_decl Sort Prop
  with path_eq_indm        := Induction for path_eq Sort Prop
  with wf_env_indm         := Induction for wf_env Sort Prop
  with wf_tp_indm          := Induction for wf_tp Sort Prop
  with wf_decl_indm        := Induction for wf_decl Sort Prop.

Combined Scheme typing_mutind from typing_indm, expands_indm, sub_tp_indm, sub_decl_indm, path_eq_indm, wf_env_indm, wf_tp_indm, wf_decl_indm.

Require Import LibTactics_sf.
Ltac mutind_typing P0_ P1_ P2_ P3_ P4_ P5_ P6_ P7_ :=
  cut ((forall E q t T (H: E |= t ~: T @ q), (P0_ E q t T H)) /\ 
  (forall E q T DS (H: E |= T ~< DS @ q), (P1_ E q T DS H)) /\ 
  (forall E q T T' (H: E |= T ~<: T' @ q), (P2_  E q T T' H))  /\ 
  (forall (e : env) (q : quality) (d d0 : decl) (H : sub_decl e q d d0), (P3_ e q d d0 H)) /\  
  (forall (e : env) (t t0 : tm) (H : path_eq e t t0), (P4_ e t t0 H)) /\  
  (forall (e : env) (H : wf_env e), (P5_ e H)) /\
  (forall (e : env) (t : tp) (H : wf_tp e t), (P6_ e t H)) /\  
  (forall (e : env) (d : decl) (H : wf_decl e d), (P7_ e d H))); [tauto | 
    apply (typing_mutind P0_ P1_ P2_ P3_ P4_ P5_ P6_ P7_); unfold P0_, P1_, P2_, P3_, P4_, P5_, P6_, P7_ in *; clear P0_ P1_ P2_ P3_ P4_ P5_ P6_ P7_; [ 
      Case "typing_var" | Case "typing_ref" | Case "typing_sel" | Case "typing_sub" | Case "typing_app" | Case "typing_lam" | Case "typing_new" | Case "expands_sub" | Case "expands_rfn" | Case "expands_and" | Case "expands_or" | Case "expands_top" | Case "sub_tp_rfn_intro" | Case "sub_tp_rfn_elim" | Case "sub_tp_rfn" | Case "sub_tp_rfn_precise" | Case "sub_tp_tpsel_lower" | Case "sub_tp_tpsel_upper" | Case "sub_tp_trans" | Case "sub_tp_path_eq" | Case "sub_tp_refl" | Case "sub_tp_top" | Case "sub_tp_bot" | Case "sub_tp_fun" | Case "sub_tp_and_r" | Case "sub_tp_or_l" | Case "sub_tp_and_l1" | Case "sub_tp_and_l2" | Case "sub_tp_or_r1" | Case "sub_tp_or_r2" | Case "sub_decl_tp" | Case "sub_decl_tm" | Case "peq_refl" | Case "peq_symm" | Case "peq_env" | Case "peq_sel" | Case "wf_env_nil" | Case "wf_env_cons" | Case "wf_rfn" | Case "wf_lam" | Case "wf_tsel" | Case "wf_tsel_cls" | Case "wf_and" | Case "wf_or" | Case "wf_bot" | Case "wf_top" | Case "wf_decl_tp" | Case "wf_decl_tm" ]; 
      introv; eauto ].

(* copy/paste from sub_tp_rfn_XXX since Combined Scheme refuses to generate the induction scheme when sub_decls is in the mix *)
Inductive sub_decls : env -> quality -> decls -> decls -> Prop :=
  | sub_decls_sub :forall L E DS1 DS2,
      LabelMapImpl.dom DS2 [<l=] LabelMapImpl.dom DS1 -> (* subsumption may lose members *)
      (forall z, z \notin L -> (forall l d1 d2, LabelMapImpl.binds l d1 DS1 -> LabelMapImpl.binds l d2 DS2 -> 
            exists q, sub_decl E q (d1 ^d^ z) (d2 ^d^ z))) ->
      sub_decls E subsumed DS1 DS2

  | sub_decls_precise : forall L E DS1 DS2,
      LabelMapImpl.dom DS2 [=l=] LabelMapImpl.dom DS1 -> (* we didn't lose any members *)
      (forall z, z \notin L -> (forall l d1 d2, LabelMapImpl.binds l d1 DS1 -> LabelMapImpl.binds l d2 DS2 ->
            sub_decl E precise (d1 ^d^ z) (d2 ^d^ z))) ->
      sub_decls E precise DS1 DS2.

Inductive wf_store : store -> Prop := 
  | wf_store_nil : wf_store nil
  | wf_store_cons_tp : forall E x Tc args,
     wf_store E ->
     (forall l v, LabelMapImpl.binds l v args -> value v) -> (* the args bind labels to values *) 
     lc_tp Tc -> concrete Tc ->
     x \notin dom E ->
     wf_store (x ~ (Tc, args) ++ E).

Reserved Notation "s |~ a ~~> b  ~| s'" (at level 60).

Inductive red : store -> tm -> store -> tm -> Prop :=
  | red_beta : forall s T t v,
     wf_store s ->
     lc_tm (lam T t) ->
     value v ->
     s |~ (app (lam T t)) v ~~> (t ^^ v) ~| s
  | red_app_fun : forall s s' t e e',
     lc_tm t ->
     s |~        e ~~> e'        ~| s' ->
     s |~  app e t ~~> app e' t  ~| s'
  | red_app_arg : forall s s' v e e',
     value v ->
     s |~        e ~~> e'        ~| s' ->
     s |~  app v e ~~> app v e'  ~| s'

  | red_sel : forall s a Tc ags l v,
     wf_store s -> 
     binds a (Tc, ags) s ->
     LabelMapImpl.binds l v ags -> 
     value v -> (* follows from store well-formedness -- need to check?? *)
     s |~ (sel (ref a) l) ~~> v ~| s
  | red_sel_tgt : forall s s' l e e',
     s |~         e ~~> e'         ~| s' ->
     s |~ (sel e l) ~~> (sel e' l) ~| s'

  | red_new : forall s Tc a ags t,
     wf_store s -> 
     lc_tm (new Tc ags t) ->
     (forall l v, LabelMapImpl.binds l v ags -> value (v ^^ (ref a))) ->
     a `notin` dom s ->
     s |~   (new Tc ags t) ~~> t ^^ (ref a)   ~| ((a ~ ((Tc, ags ^args^ (ref a)))) ++ s)

where "s |~ a ~~> b  ~| s'" := (red s a s' b).



(*Definition sto_typing P mu :=
     sto_ok mu 
  /\ (forall l, l # mu -> l # P)
  /\ (forall l T, binds l T P -> 
        exists t, binds l t mu
               /\ empty ! P |= t ~: T).*)
Definition typing_store G s :=
     wf_store s 
  /\ (forall a Tc argsRT, binds a (Tc, argsRT) s ->  (* TODO: don't need Tc in store since Gamma it -- bound in store to args with type Tc, where the self variable has been replaced by `a` already  *) 
              exists args, argsRT = args ^args^ (ref a)  (* concentrate the burden of uniqueness of store bindings in typing_new case of preservation *)
          /\  concrete Tc (* see typing_new, replacing implication by conjunction and forall by exists *)
          /\  LabelMapImpl.uniq args (* ctor args are unique by label *)
          /\  exists ds, (G, s) |= Tc ~< ds @ precise
          /\  (LabelMapImpl.dom ds) [=l=] (LabelMapImpl.dom args) (* all ctor args must have declaration with same label*)
          /\  (exists L, (forall x, x \notin L -> (forall l d, LabelMapImpl.binds l d ds -> 
                (forall U T, d ^d^ x = decl_tp T U -> (exists q, (ctx_bind (G, s) x Tc) |= T ~<: U @ q)) /\ (* for each type member: its lower bound must be a subtype of its upper bound *)
                (forall T, d ^d^ x = decl_tm T -> (exists v,  (* for each term member there's a ctor argument with the same label that provides a well-typed value *)
                  LabelMapImpl.binds l v args /\ value (v ^^ x) /\ (exists q, (ctx_bind (G, s) x Tc) |= (v ^^ x) ~: T @ q)))))
              )).
(* subsumed by (G, s) |= (ref a) ~: Tc @ precise:
   (* must be able to derive a typing judgement for (ref a) for every location a in the store
  there are no reduction steps under binders, except for the variables representing object references, but these are of course also in the store this ensures that for all x: T in E, the T's well-formedness has been checked by typing_new *)
*)

Notation "E |== s" := (typing_store E s) (at level 68).

(* need to leave some quality-slack here since otherwise preservation/t-sel/e-sel isn't provable: 
   a.l ~~> v does not preserve quality, since a.l may be typed precisely but v's typing comes from T-new, which has to allow subsumption
   quality slack should be okay though, since e.g. the reduction e.l -> e'.l can still reuse the expansion of the typing of e.l since e' has the same type as e, the quality doesn't matter
*)

(* XXX TODO: not urgent since E does not change during preservation (only s does), but must require
   forall x T DS q, binds x T E /\ (E, s) |= T ~< DS @ q -> (forall l d, LabelMapImpl.binds l d DS -> 
  (forall U T, d ^d^ x = decl_tp T U -> (exists q, (ctx_bind (E, s) x Tc) |= T ~<: U @ q))) 
*)
Definition preservation := forall E_s q t T, E_s |=  t ~: T  @ q -> forall E t' s s', E_s = (E, s) -> 
  E |== s -> s  |~  t ~~> t'  ~| s' -> (E |== s' /\ exists q', (E, s') |=  t' ~: T @ q'). 

Definition progress := forall s t T q,
  (nil, s) |=  t ~: T @ q ->
  nil |== s ->
     value t \/ exists t', exists s', s |~ t ~~> t' ~| s'.



(* trips up combined scheme -- sub_decls was factored into sub_tp since coq can't handle the resulting combined scheme  -- some weird error in decomposing products
  | sub_tp_rfn_sub : forall L E q T DS1 DS2,
      (forall z, z \notin L -> sub_decls (ctx_bind E z T) q (DS1 ^ds^ z) (DS2 ^ds^ z)) ->
      sub_tp E q (tp_rfn T DS1) (tp_rfn T DS2)

with sub_decls : env -> quality -> decls -> decls -> Prop :=
  | sub_decls_precise : forall E DS1 DS2,
      (forall d2, In d2 DS2 -> (exists d1, In d1 DS1 /\ sub_decl E precise d1 d2))  ->
      (forall d1, In d1 DS1 -> (exists d2, In d2 DS2 /\ same_label d1 d2)) ->
      sub_decls E precise DS1 DS2
  | sub_decls_subsumed : forall E DS1 DS2,
      (forall d2, In d2 DS2 -> (exists d1, exists q, In d1 DS1 /\ sub_decl E q d1 d2)) ->
      sub_decls E subsumed DS1 DS2
*)  


(*
Inductive safe_path : env -> tm -> Prop :=
   | safe_path_ref_ok : forall E a T,
      ctx_binds_ok E a T ->
      safe_path E (ref a)
   | safe_path_fvar_ok : forall E x T,
      ctx_binds_ok E x T ->
      safe_path E (fvar x)
   | safe_path_sel : forall E p l,
      safe_path E p -> safe_path E (sel p l).

Notation "E |= t 'safe'" := (safe_path E t) (at level 69).

Definition extract_pex : loc -> args -> pex := fun a => fun ags =>
  List.flat_map (fun l_v => match l_v with 
       | (l, ref al) => (al, (a, l)) :: nil
       | _ => nil
       end) ags.

*)


(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "../metalib") ***
*** End: ***
*)  