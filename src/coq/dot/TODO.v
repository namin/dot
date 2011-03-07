Lemma invert_typing_sel: forall E t l T q s, E |== s -> (E, s) |= sel t l ~: T @ q ->   
      exists T', exists q1, (E, s) |= t ~: T' @ q1 /\
      exists DS, exists q2, (E, s) |= T' ~< DS @ q2 /\
      exists D, lbl.binds l D DS /\
      exists S, open_decl_cond D t (decl_tm S) /\
      exists q3, (E, s) |= S ~<: T @ q3.
Proof.

Lemma subst_pres_typing : forall E x Tx t T v, 
  (exists q, ctx_bind E x Tx |= t ^^ x ~: T ^tp^ x @ q)
  -> value v 
  -> (exists q, E |= v ~: Tx @ q)
  -> exists q, E |= (t ^^ v) ~: (T ^tp^ v) @ q.
Proof. Admitted.

(* XXXX probably not provable as-is: what if E has an evil variable binding? that could be used to create an illegal subtyping derivation *)
Lemma sub_tp_trans_safe : forall E s S TMid T q1 q2, E |== s -> (E, s) |= S ~<: TMid @ q1 -> (E, s) |= TMid ~<: T @ q2 -> exists q3, (E, s) |= S ~<: T @ q3.
Proof. Admitted. (* intros.  set TMid as TMid'. destruct TMid; try solve [exists (q1 & q2); apply sub_tp_trans with (TMid := TMid'); auto; unfold not; intros ? ? HH; inversion HH | idtac]. clear TMid'.   dependent induction H0.*)

Lemma expands_sub_safe : forall E s S TMid DS q1 q2, E |== s -> (E, s) |= S ~<: TMid @ q1 -> (E, s) |= TMid ~< DS @ q2 -> exists q3, (E, s) |= S ~< DS @ q3.
Proof. Admitted.

Lemma invert_expands_concrete : forall E s Tc DS q, (E, s) |= Tc ~< DS @ q -> concrete Tc -> 
    exists DS', (E, s) |= Tc ~< DS' @ precise /\ exists q, sub_decls (E, s) q DS' DS.
Proof. Admitted.


Theorem quality_soundness : forall E T DS DSp, 
  (exists q, E |= T ~< DS @ q) ->  E |= T ~< DSp @ precise -> E |= DSp <:DS<: DS.
Proof. Admitted.
  Lemma quality_soundness_sub : forall E DS DS' T U q1 q2, 
    E |= T ~< DS @ precise -> 
    E |= T ~<: U @ q1 -> 
    E |= U ~< DS' @ q2 /\
    E |= DS <:DS<: DS'.
  Proof. Admitted. 


Lemma invert_subtyping_top : 
   (forall E q T DS, E |= T ~< DS @ q -> subsumes_top T -> DS = nil) /\
   (forall E q T T', E |= T ~<: T' @ q -> subsumes_top T -> ~ has_tp_sel T' -> subsumes_top T').
Proof. Admitted.


Lemma invert_expands_fun: forall E S T DS q,  E |= tp_fun S T ~< DS @ q -> DS = nil.
Proof. Admitted.

Lemma invert_subtyping_fun : 
   (forall E q T DS, E |= T ~< DS @ q -> exists T1, exists T2, subsumes_fun_tp T T1 T2 -> DS = nil) /\
   (forall E q T T', E |= T ~<: T' @ q -> forall T1 T2, subsumes_fun_tp T T1 T2 -> ~ has_tp_sel T' -> exists T1', exists T2', subsumes_fun_tp T' T1' T2' /\ exists q, E |= T1' ~<: T1 @ q /\ exists q, E |= T2 ~<: T2' @ q).
Proof. Admitted.

Lemma invert_subtyping_and_l : forall E T1 T2 T q, E |= tp_and T1 T2 ~<: T @ q -> 
  (exists q, E |= T1 ~<: T @ q) /\ (exists q, E |= T2 ~<: T @ q).
Proof. Admitted.


Lemma invert_typing_lam : forall E S t U q s, E |== s -> (E, s) |= lam S t ~: U @ q -> 
      exists q1, exists L, exists T, (forall x, x \notin L -> (ctx_bind (E, s) x S) |= (t ^^ x) ~: T @ q1) /\
      wf_tp (E, s) (tp_fun S T) /\ lc_tp T /\
      exists q2, (E, s) |= (tp_fun S T) ~<: U @ q2.
Proof. Admitted.

Lemma invert_typing_ref: forall E s a T q, (E, s) |= ref a ~: T @ q -> 
    exists T', exists args, binds a (T', args) s /\
    exists q, (E, s) |= T' ~<: T @ q.
Proof. Admitted.


Lemma invert_red_store_dom : forall s t t' s', s |~ t ~~> t' ~| s' -> dom s [<=] dom s'.
Proof. Admitted.


Lemma invert_wf_store_uniq : forall s, wf_store s -> uniq s.
Proof. Admitted.


Lemma or_decls_nil_2 : forall ds1 ds2 ds, or_decls ds1 ds2 ds -> ds1 = nil \/ ds2 = nil -> ds = nil.
Proof. Admitted.

Lemma red_implies_peq: forall E s t t' s', E |== s' -> s |~ t ~~> t' ~| s' -> path t -> path t' -> path_eq (E, s') t t'. 
Proof. Admitted.

Lemma sub_decls_pres_binds : forall l D DS E DS' q,
    lbl.binds l D DS -> sub_decls E q DS' DS -> 
      exists D', exists q, lbl.binds l D' DS' /\ sub_decl E q D' D.
Proof. Admitted.


Lemma sub_decls_monotone_or_2 : forall E DS DS' DX DX' DSX DSX', 
  E |= DS <:DS<: DS' ->     E |= DX <:DS<: DX' -> 
  or_decls DS  DX DSX -> or_decls DS' DX' DSX' -> 
  E |= DSX <:DS<: DSX'.
  Proof. Admitted.

Lemma sub_decls_monotone_and_2 : forall E DS DS' DX DX' DSX DSX', 
  E |= DS <:DS<: DS' ->     E |= DX <:DS<: DX' -> 
  and_decls DS  DX DSX -> and_decls DS' DX' DSX' -> 
  E |= DSX <:DS<: DSX'.
  Proof. Admitted.

Lemma sub_decls_monotone_and : forall E DS DS' DX DSX DSX', 
  E |= DS <:DS<: DS' -> 
  and_decls DS  DX DSX -> and_decls DS' DX DSX' -> 
  E |= DSX <:DS<: DSX'.
  Proof. Admitted.



Lemma open_lc_decl_ident: forall d t, lc_decl d -> open_decl_cond d t d. Proof. Admitted.
Lemma open_lc_is_noop : forall T x, lc_tp T -> T = T ^tp^ x. Proof. Admitted.

Lemma binds_map_3 : forall A B l v (f: A -> B) args, lbl.binds l v ((lbl.map f) args) -> exists v', lbl.binds l v' args.
Proof. Admitted.
