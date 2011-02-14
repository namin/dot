(*************************************************************************)
(** Miscellaneous helper functions and lemmas                            *)
(** Author: Adriaan Moors, 2008                                          *)
(*************************************************************************)
Set Implicit Arguments.

Require Import List.
Require Import Metatheory.


Section ReDunModulo.

  Variable A : Type.
  Variable B : Type.
  Variable modulo : A -> B.

  Inductive NoDupBy : list A -> Prop :=
    | NoDupBy_nil : NoDupBy nil
    | NoDupBy_cons : forall x (l: list A), ~ In (modulo x) (List.map modulo l) -> NoDupBy l -> NoDupBy (x::l).
(*
  Lemma NoDupBy_remove_1 : forall l l' a, NoDupBy (l++a::l') -> NoDupBy (l++l').

  Lemma NoDupBy_remove_2 : forall l l' a, NoDupBy (l++a::l') -> ~In a (l++l').
*)
End ReDunModulo.

(*Fixpoint option_getOrElse (A: Set) (alt: A) (o: option A)  : A :=
  match o with
    | None => alt
    | (Some x) => x
  end.

Implicit Arguments option_getOrElse [A].
*)

Definition option_bind (A:Type) (B:Type) (f: A-> option B) (o: option A) :=
  match o with
  | None => None
  | Some x => f x
  end.

Definition option_fold (A:Type) (B:Type) (f:A->B) (b:B) o :=
  match o with
  | None => b
  | Some x => f x
  end.

Implicit Arguments option_fold [A B].



Fixpoint option_forAll (o: option Prop): Prop :=
  match o with
    | None => True 
    | (Some x) => x
  end.

Definition option_has (A: Type) (x: A) (o: option A) 
  := option_fold (fun x' => x = x') (False) o.


(** weird that I couldn't find this in StdLib *)
Fixpoint list_forAll (l: list Prop): Prop :=
  match l with
    | (cons x xs) => x /\ (list_forAll xs)
    | nil => True
  end.

Lemma under_forAll_map: forall (A: Set) (xs: list A) (f g : A -> Prop),
  (forall x : A, f x -> g x) -> (list_forAll (List.map f xs)) -> (list_forAll (List.map g xs)).
  intros.
  induction xs; simpl in *; auto.
    inversion H0. split.
      apply (H a H1).
      apply (IHxs H2).
Qed.    
    

Lemma under_forAll_map_retain_in: forall (A: Set) (xs: list A) (f g : A -> Prop),
  (forall x : A, In x xs -> f x -> g x) -> (list_forAll (List.map f xs)) -> (list_forAll (List.map g xs)).
  intros.
  induction xs; auto. (*simpl. split. simpl in H0. destruct H0. apply (H a). simpl. left. auto. assumption.*)

    induction H0; auto; simpl in *.
      split. apply (H a). auto. assumption.
      assert (forall x : A, In x xs -> f x -> g x) as Htl.
        intros. apply H. auto. assumption.
      apply (IHxs Htl). assumption.
Qed.   

Lemma forAll_implies_forIn: forall (A: Set) (xs: list A) x f,
  list_forAll (List.map f xs) -> In x xs -> f x.
Proof.
  intros. induction xs. simpl in H0. contradiction. 
    simpl in *. destruct H. inversion H0. subst. assumption.
      apply (IHxs H1 H2).
Qed.



(** TODO: use under_forAll_map **)
Lemma list_forAll_MP: forall (A : Set) (l : list A)  (P: A -> Prop) (Q: A -> Prop),
    list_forAll (List.map (fun x: A => P x -> Q x) l) -> list_forAll (List.map (fun x: A => P x) l) -> list_forAll (List.map (fun x: A => Q x) l).
Proof.
  intros A l P Q H.
  induction l. simpl. auto. simpl. induction H. split. apply H. destruct H1. assumption. destruct H1. apply (IHl H0 H2).
Qed.

Lemma list_forAll_eq_dist : forall (A : Set) (l : list A)  (f: A -> A),
  list_forAll (List.map (fun x : A => f x = x) l) -> List.map f l = l.
Proof.
  intros A l f H.
  induction l. 
    auto.
 
    simpl in *. 
      induction H. 
        rewrite H. f_equal. apply (IHl H0).
Qed.

Lemma list_forAll_eq_dist2 : forall (A : Set) (l : list A)  (f: A -> A) (g: A -> A),
  list_forAll (List.map (fun x : A => f x = g x) l) -> List.map f l = List.map g l.
Proof.
  intros A l f g H.
  induction l. 
    auto.
 
    simpl in *. 
      induction H. 
        rewrite H. f_equal. apply (IHl H0).
Qed.

Lemma list_forAll_eq_dist2_conv : forall (A : Set) (l : list A)  (f: A -> A) (g: A -> A),
  List.map f l = List.map g l -> list_forAll (List.map (fun x : A => f x = g x) l).
Proof.
  intros A l f g H.
  induction l; simpl in *. 
    auto.

  inversion H. split.  auto. apply IHl. assumption.
Qed.

Functional Scheme fold_left_ind := Induction for fold_left Sort Prop.

(*
Lemma foldUnionAssoc: forall A (f: A -> vars) (xs: list A) (x: A),
 fold_left (fun (xs : vars) (x : A) => xs \u f x)
                xs ({} \u f x) 
   =  fold_left (fun (xs : vars) (x : A) => xs \u f x)
                xs {} \u f x.
Proof.
  intros. functional induction (fold_left  (fun (xs : vars) (x : A) => xs \u f x)
                xs {}).
  simpl. auto.
  simpl. replace ((a0 \u f x) \u f b) with ((a0 \u f b) \u f x). assumption.

  rewrite union_comm.
  rewrite union_comm_assoc.
  rewrite union_assoc.
  reflexivity.  
Qed.

Lemma notinUnion_forAll_notin: forall (A: Set) (xs: list A) x (f: A -> vars),
  x \notin (fold_left (fun (ats: vars) (m : A) => ats \u f m) xs {})
 -> list_forAll (List.map (fun m : A => x \notin f m) xs).
Proof.
  intros. induction xs. simpl. auto. simpl in *. 
     split;
        pattern (fold_left (fun (ats : vars) (m : A) => ats \u f m)
                xs ({} \u f a)) in H;
        rewrite (foldUnionAssoc f xs a) in H.
           auto.
           apply IHxs. auto.
Qed.

Lemma notin_fold_left_monotone: forall (A: Set) (xs: list A) x (f: A -> vars) Vars,
  x \notin (fold_left (fun (ats: vars) (m : A) => ats \u f m) xs Vars)
  -> x \notin Vars.
Proof.
  intros.
  functional induction (fold_left (fun (ats : vars) (m : A) => ats \u f m) xs Vars); trivial.
  pose (IHp H). auto.
Qed.

Lemma notin_fold_left_monotone2: forall (A: Set) y (ys: list A) x (f: A -> vars),
  x \notin (fold_left (fun (ats: vars) (m : A) => ats \u f m) (y :: ys) {})
->  x \notin (fold_left (fun (ats: vars) (m : A) => ats \u f m) ys {}).
Proof.
  intros.
  functional induction (fold_left (fun (ats : vars) (m : A) => ats \u f m) (ys) {}); trivial.
  apply (notin_fold_left_monotone _ _ H).
  simpl in *.
  replace (a0 \u f y \u f b) with (a0 \u f b \u f y) in H.
  pose (IHp H). auto. 
  rewrite union_comm. rewrite union_comm_assoc. rewrite union_assoc. trivial.
Qed.
*)

(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "../metalib") ***
*** End: ***
*)