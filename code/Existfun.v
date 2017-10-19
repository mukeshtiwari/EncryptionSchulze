Require Import Notations.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Le.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.omega.Omega.
Require Import Bool.Sumbool.
Require Import Bool.Bool.
Require Import Coq.Logic.ConstructiveEpsilon.
Require Import Permutation.
(* Require Import Coq.ZArith.ZArith.
 Require Import ListLemma. *)
Import ListNotations.
Require Import
        Program Morphisms Relations RelationClasses Permutation.


Notation "'existsT' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'existsT' '/ ' x .. y , '/ ' p ']'") : type_scope.


Lemma filter_empty : forall (A : Type) (l : list A) (f : A -> bool),
    filter f l = [] <->
    (forall x, In x l -> f x = false).
Proof.
  intros A. induction l.
  split; intros. inversion H0. reflexivity.
  split; intros. destruct H0. simpl in H.
  destruct (f a) eqn : Ht. inversion H.
  rewrite <- H0. assumption.
  simpl in H. destruct (f a). inversion H.
  pose proof (proj1 (IHl f) H x H0). assumption.
  simpl. destruct (f a) eqn: Ht.
  pose proof (H a (in_eq a l)). congruence.
  pose proof (IHl f). destruct H0.
  apply H1. intros. firstorder.
Qed.


Lemma complementary_filter_perm A (p: A -> bool) (l: list A):
  Permutation l (filter p l ++ filter (compose negb p) l).
Proof with auto.
  induction l...
  simpl.
  unfold compose.
  destruct (p a); simpl...
  apply Permutation_cons_app...
Qed.

Lemma complementary_filter_In : forall
    (A : Type) (l : list A) (f : A -> bool) (g : A -> bool)
    (H : forall x, In x l -> f x = negb (g x)),
    Permutation l (filter f l ++ filter g l).
Proof with auto.
  intros A l f g H.
  induction l...
  simpl.
  destruct (f a) eqn : Ht; simpl...
  pose proof (H a (in_eq a l)).
  rewrite Ht in H0.
  SearchAbout ( negb _ = true). symmetry in H0.
  apply negb_true_iff in H0.
  rewrite H0. apply perm_skip. apply IHl.
  intros. apply H. simpl. right. auto.
  pose proof (H a (in_eq a l)).
  rewrite Ht in H0. symmetry in H0. apply negb_false_iff in H0.
  rewrite H0.
  apply Permutation_cons_app...
  apply IHl. intros.
  apply H. simpl. right. auto.
Qed.



Section Cand.

  Variable A : Type.
  Variable P : A -> A -> Prop.
  Hypothesis Adec : forall (c d : A), {c = d} + {c <> d}. (* A is decidable *)
  Hypothesis Pdec : forall c d, {P c d} + {~P c d}. (* P is decidable *)


  (* A is finite. finite : Type -> Type *)
  Definition finite := existsT (l : list A), forall (a : A), In a l.

  (* vl : forall A : Type, (P : A -> A -> Prop) -> (list A) -> Prop *)
  Definition vl (l : list A) :=
    exists (f : A -> nat), forall (c d : A), In c l -> In d l -> (P c d <-> (f c < f d)%nat).


  Fixpoint listmax (f : A -> nat) (l : list A): nat :=
    match l with
    | [] => O
    | [h] => f h
    | h :: t => max (f h) (listmax f t)
    end.

 
  Lemma listmax_upperbound :
    forall (l : list A) (d : A) (f : A -> nat) (Hin : In d l),
      f d <= listmax f l.
  Proof.
    induction l.
    intros. inversion Hin.

    intros d f Hin.
    assert (Hm : {f a >= listmax f l} + {f a < listmax f l}).
    pose proof (lt_eq_lt_dec (f a) (listmax f l)) as H1.
    destruct H1 as [[H1 | H1] | H1]. right. auto.
    left. omega. left. omega.

    assert (Ht : listmax f (a :: l) = max (f a) (listmax f l)).
    simpl. destruct l. simpl. SearchAbout (max _ 0 = _).
    rewrite Max.max_0_r. auto. auto.

    rewrite Ht. clear Ht.
    destruct Hin. destruct Hm. rewrite H.
    apply Max.le_max_l.
    rewrite H. apply Max.le_max_l.
    destruct Hm.

    pose proof (IHl d f H).
    rewrite Max.max_l. omega. omega.
    rewrite Max.max_r.
    pose proof (IHl d f H).
    omega. omega.
  Qed.
  
 
    
    
  
  Lemma validity_after_remove_cand :
    forall (l : list A) (a0 : A),
      vl (a0 :: l) <->
      vl l /\ ~P a0 a0 /\
      (forall (c e : A), In c l -> In e l ->  P c a0 -> P a0 e -> P c e) /\
      ((exists (a0' : A), In a0' l /\ forall (x : A), In x l -> (P a0 x <-> P a0' x) /\
                                                                (P x a0 <-> P x a0')) \/
       (* forall (x : A), In x l -> P x a0 \/ P a0 x *)
       (forall (x : A), In x l -> (P x a0 /\ ~P a0 x)
                                  \/ (P a0 x /\  ~P x a0))
      ).
  Proof.
    unfold vl; split; intros.
    destruct H as [f H].
    split.
    exists f. firstorder.

    split. unfold not. intros. pose proof (proj1 (H a0 a0 (in_eq a0 l) (in_eq a0 l)) H0).
    omega.

    split. intros.
    pose proof (H c a0 (in_cons _ c l H0) (in_eq a0 l)).
    pose proof (H a0 e (in_eq a0 l) (in_cons _ e l H1)).
    firstorder.

    assert (Hnat : forall x y : nat, {x = y} + {x <> y}) by (auto with arith).

    pose proof (in_dec Hnat (f a0) (map f l)).  clear Hnat.
    destruct H0.
    apply in_map_iff in i. destruct i as [a [Hl Hr]].
    (* I know the exitence of element which is in l and equal to f a0 *)
    left. exists a. split. assumption.
    intros x Hx. split. split; intros.

    pose proof (H a0 x (in_eq a0 l) (or_intror Hx)).
    firstorder.

    pose proof (H a x (or_intror Hr) (or_intror Hx)).
    firstorder.

    split; intros.

    pose proof (H x a0 (or_intror Hx) (in_eq a0 l)).
    firstorder.

    pose proof (H x a (or_intror Hx) (or_intror Hr)).
    firstorder.

    (* time to go right *)
    right.
    intros x Hx.

    destruct (lt_eq_lt_dec (f a0) (f x)) as [[H1 | H1] | H1].
    pose proof (H a0 x (in_eq a0 l) (or_intror Hx)).
    right. split. firstorder. firstorder.

    (* f a0 can't be equal to f x *)
    assert (Ht : f a0 <> f x).
    induction l. inversion Hx.

    apply not_in_cons in n.
    destruct n. destruct Hx. rewrite <- H3 in H1.
    omega.

    apply IHl. intros.
    firstorder. assumption. assumption.
    omega.

    pose proof (H x a0 (or_intror Hx) (in_eq a0 l)).
    firstorder.

    (* finally finished the first half. feeling great :) *)

    destruct H as [[f H1] [Ht [Ht1 [[a [H2 H3]] | H2]]]].
    (* From H3, I know that f a = f a0  so I am going to supply same function *)

    exists (fun c => if Adec c a0 then f a else f c). intros c d H4 H5. destruct H4, H5.
    split; intros.
    rewrite <- H in H4. rewrite <- H0 in H4.
    firstorder. rewrite <- H0 in H4.
    rewrite -> H in H4. omega.

    split; intros.
    rewrite <- H. destruct (Adec a0 a0).
    destruct (Adec d a0).
    congruence.
    subst. firstorder.
    congruence. subst.
    destruct (Adec c c). destruct (Adec d c).
    omega. firstorder.
    firstorder.

    split; intros.
    subst. destruct (Adec c d). destruct (Adec d d).
    subst. congruence.
    firstorder. destruct (Adec d d). firstorder.
    firstorder. destruct (Adec c a0). destruct (Adec d a0).
    firstorder. subst. firstorder.
    subst. destruct (Adec d d). firstorder.
    firstorder.

    split; intros.
    destruct (Adec c a0). destruct (Adec d a0).
    subst. firstorder.
    subst. firstorder.
    destruct (Adec d a0).
    subst. firstorder.
    firstorder.

    destruct (Adec c a0). destruct (Adec d a0).
    subst. firstorder.
    subst. firstorder.
    destruct (Adec d a0).
    subst. firstorder.
    subst. firstorder.

    
    remember (filter (fun y => if Pdec y a0 then true else false) l) as l1.
    remember (filter (fun y => if Pdec a0 y then true else false) l) as l2.
    assert (Ht2 : forall x, In x l1 -> P x a0 /\ ~P a0 x).
    intros. rewrite Heql1 in H.
    pose proof (proj1 (filter_In _ _ _) H).
    destruct H0. pose proof (H2 x H0). destruct H4. auto.
    destruct (Pdec x a0).  firstorder.  inversion H3.
    assert (Ht3 : forall x, In x l2 -> P a0 x /\ ~P x a0).
    intros. rewrite Heql2 in H.
    pose proof (proj1 (filter_In _ _ _) H).
    destruct H0. pose proof (H2 x H0). destruct H4.
    destruct (Pdec a0 x). firstorder. inversion H3. auto.
    remember (fun y : A => if Pdec y a0 then true else false) as f1.
    remember (fun y : A => if Pdec a0 y then true else false) as g1.
    assert (Ht4 : forall x, In x l -> f1 x = negb (g1 x)).
    intros.
    rewrite Heqf1.
    rewrite Heqg1.
    destruct (Pdec x a0) eqn: Ht4.
    destruct (Pdec a0 x) eqn: Ht5.
    pose proof (H2 x H). destruct H0.
    firstorder. firstorder.
    auto.
    destruct (Pdec a0 x) eqn: Ht6. auto.
    pose proof (H2 x H). destruct H0.
    firstorder. firstorder.
    pose proof (complementary_filter_In _ l f1 g1 Ht4).
    rewrite <- Heql1 in H. rewrite <- Heql2 in H. 
 
    (* for a0,  take maximum of all the candidates which is preferred over
       a0 and add one to it.
       a1, a2 ......, a0, ....., an
       We don't need to change the values for candidates preferred over a0, but
       those who are less preferred over a0 should be shifted by 1 *)

    
    exists (fun x =>
              match Adec x a0 with
              | left _ =>
                plus (S O)
                     (listmax f (filter (fun y => if Pdec y a0 then true else false) l))
              | right _ =>
                if andb (if Pdec a0 x then true else false)
                        (if (in_dec Adec x l) then true else false)
                then plus (S (S O)) (f x)
                else  (f x)
              end).

    (* this code is for permuation of list *)
     
    split; intros.
    destruct H0, H3.
    (* c = a0 and d = a0 *)
    congruence.

    (* c = a0 and In d l *)
    rewrite <- H0. rewrite <- H0 in H4.
    destruct (Adec a0 a0).
    destruct (Adec d a0).
    congruence.
    destruct (Pdec a0 d).
    destruct (in_dec Adec d l).
    simpl. apply lt_n_S.
 
    (* remove unnecessary assumption *)
    clear e. clear p. clear i. clear n.
    pose proof Permutation_in. 
    pose proof (H5 A l (l1 ++ l2) d H H3).
    apply in_app_iff in H6. destruct H6.
    pose proof (Ht2 d H6). firstorder.
    rewrite <- Heqf1.
    rewrite <- Heql1.
    
    assert (Ht5: forall x, In x l1 -> forall y, In y l2 -> f x < f y).
    intros. apply H1.
    apply Permutation_sym in H.
    pose proof (H5 A (l1 ++ l2) l x H). apply H9.
    firstorder.
    apply Permutation_sym in H.
    pose proof (H5 A (l1 ++ l2) l y H). apply H9.
    firstorder.
    apply Ht1.
    apply Permutation_sym in H.
    pose proof (H5 A (l1 ++ l2) l x H). apply H9.
    firstorder.
    apply Permutation_sym in H.
    pose proof (H5 A (l1 ++ l2) l y H). apply H9.
    firstorder. firstorder. firstorder.
    
    clear H. clear H5. clear Heql1. clear Ht2.
    induction l1. simpl. omega.
    simpl. destruct l1.
    pose proof (Ht5 a (in_eq a []) d H6). omega.
    apply Nat.max_lub_lt_iff. split.
    pose proof (Ht5 a (in_eq a (a1 :: l1)) d H6).
    omega. apply IHl1. firstorder.

    congruence.  congruence. congruence.

    (* In c l and d = a0 *)
    
    rewrite <- H3. rewrite <- H3 in H4.
    destruct (Adec c a0). destruct (Adec a0 a0).
    congruence. congruence.
    destruct (Pdec a0 c). destruct (in_dec Adec c l).
    destruct (Adec a0 a0). simpl. apply lt_n_S.

    clear i. clear e. clear n.
    pose proof (H2 c H0). firstorder.
    congruence. congruence.
    simpl. destruct (Adec a0 a0).

    clear e. clear n.
    pose proof Permutation_in.
    pose proof (H5 A l (l1 ++ l2) c H H0).
    apply in_app_iff in H6. destruct H6.
    pose proof (Ht2 c H6). 
    rewrite <- Heqf1.
    rewrite <- Heql1.

    clear H. clear Heql1. clear Ht2. clear H5.     
    
    
    induction l1.
    inversion H6.

    simpl. destruct l1.
    destruct H6. rewrite H. omega. inversion H.
    pose proof (Max.max_dec (f a) (listmax f (a1 :: l1))).
    destruct H as [H | H].
    rewrite H.
    destruct H6. rewrite H5. omega.
    pose proof (IHl1 H5).
    apply Nat.max_l_iff in H. omega.
    rewrite H. destruct H6.
    rewrite <- H5.
    apply Nat.max_r_iff in H. omega.
    pose proof (IHl1 H5). assumption.
    firstorder. congruence.
  
    (* In c l and In d l *)
    destruct (Adec c a0).
    destruct (Adec d a0).
    congruence. rewrite e in H0.
    pose proof (H2 a0 H0). firstorder.    
    simpl.
    destruct (Pdec a0 c).
    destruct (in_dec Adec c l). simpl.
    destruct (Adec d a0).
    rewrite e in H3.
    pose proof (H2 a0 H3). firstorder.
    destruct (Pdec a0 d).
    destruct (in_dec Adec d l). simpl.
    repeat apply lt_n_S. firstorder.
    congruence. simpl.

    pose proof (H2 c H0).
    pose proof (H2 d H3).
    destruct H5, H6.
    destruct H5. destruct H6. firstorder.
    firstorder.
    destruct H5. destruct H6.
    pose proof (Ht1 d c H3 H0 H6 H5).
    pose proof (proj1 (H1 c d H0 H3) H4).
    pose proof (proj1 (H1 d c H3 H0) H9).
    omega.
    destruct H5. destruct H6. firstorder.
    firstorder. simpl.
    destruct (Adec d a0).
    rewrite e in H3.
    pose proof (H2 a0 H3). firstorder.
    destruct (Pdec a0 d).
    destruct (in_dec Adec d l).
    simpl. pose proof (proj1 (H1 c d H0 H3) H4). firstorder.
    congruence. simpl. firstorder.

    pose proof Permutation_in.
    
    
  

    

    
    (* other side of proof *)
    destruct H0, H3. 
    (* c = a0 and d = a0 *)
    rewrite <- H0 in H4.
    rewrite <- H3 in H4. omega.
   
    (* c = a0 and In d l *)
    rewrite <- H0 in H4.
    destruct (Adec a0 a0).
    destruct (Adec d a0). omega.
    destruct (Pdec a0 d).
    destruct (in_dec Adec d l).
    simpl in H4. apply lt_S_n in H4.
    clear e. clear n. clear i.
    rewrite <- Heqf1 in H4.
    rewrite <- Heql1 in H4.
    rewrite <- H0. assumption.
    congruence. simpl in H4.
    clear e. clear n.
    pose proof (H2 d H3). destruct H6.
    destruct H6. clear n0.
    pose proof (H5 A _ _ d H H3).
    apply in_app_iff in H8. destruct H8.


    assert (Ht5: forall x, In x l1 -> forall y, In y l2 -> f x < f y).
    intros. apply H1.
    apply Permutation_sym in H.
    pose proof (H5 A (l1 ++ l2) l x H). apply H11.
    firstorder.
    apply Permutation_sym in H.
    pose proof (H5 A (l1 ++ l2) l y H). apply H11.
    firstorder.
    apply Ht1.
    apply Permutation_sym in H.
    pose proof (H5 A (l1 ++ l2) l x H). apply H11.
    firstorder.
    apply Permutation_sym in H.
    pose proof (H5 A (l1 ++ l2) l y H). apply H11.
    firstorder. firstorder. firstorder.

    rewrite <- Heqf1 in H4. rewrite <- Heql1 in H4.
    pose proof (listmax_upperbound l1 d f H8). omega.
    firstorder. firstorder. firstorder.

    
   
    
    
    
    (* This proof is mostly followed by validity_after_remove_cand. *)
    Lemma vl_or_notvl : forall l : list A, vl l + ~vl l.
    Proof.

      induction l.
      left. unfold vl. eexists.
      intros c d Hc Hd; inversion Hc.

      (* l := a :: l *)
      pose proof (validity_after_remove_cand l a).
      destruct IHl.
      (* if P a a or ~ P a a *)
      pose proof (Pdec a a).
      (* I can not destruct H0 of type Prop because goal is of type Set.
       We need to probably change the Pdec to forall c d, {P c d} + {~ P c d} ? *)
      (* After this proof is very easy.
       If P a a then we can not construct the valid (a :: l) from vl and go right.
       If ~P a a then we can construct the the valid (a :: l) from vl.
       In (f a) (map f l) + ~ In (f a) (map f l).
       If In (f a) (map f l) then we there is some element, a0, in l such that
       f a = f a0 and we can  discharge existential
       If ~In (f a) (map f l) then we can split the l into two sorted list, l1 , l2
       and discharge forall x, In x l -> P a x \/ P x a *)


      (* if ~vl l then adding candidate would also not make it valid
       got for right *)
      admit.
      right. unfold not. intros.
      destruct n. firstorder.
    Admitted.



    Definition valid := exists (f : A -> nat), forall (c d : A), P c d <-> (f c < f d)%nat.

    Lemma from_vl_to_valid : forall (l : list A), ((forall a : A, In a l) -> valid <-> vl l).
    Proof.
      intros l Ha. split; intros.
      unfold valid in H.
      unfold vl.
      destruct H as [f H].
      firstorder.
      unfold vl in H. unfold valid.
      destruct H as [f H].
      exists f. split; intros.
      apply H; auto.
      apply H; auto.
    Qed.


    Lemma decidable_valid : finite -> {valid} + {~valid}.
    Proof.
      unfold finite, valid.
      intros H. destruct H as [l Hin].




End Cand.

Check decidable_valid.





Lemma validity_after_remove_cand :
  forall (P : A -> A -> Prop) (l : list A) (Hpdec : forall c d, P c d \/ ~P c d),
    valid P l <->
    exists (c : A), forall (d : A), In c l /\ In d l /\  (equal_rank P c d \/ (P c d \/ c = d \/ P d c))
                                    /\ valid P (remove A_dec d l).
Proof.
  unfold valid, equal_rank.
  split; intros.
  destruct H as [f H].

  (* induction on l *)
  induction l.
  (* admit the empty case for the moment *)
  admit.
  (* a :: l and assume c = a *)
  exists a. intros d.
  (* Either d is a or d is inside the list *)
  destruct (A_dec a d).
  split. apply in_eq.
  split. firstorder.
  split. (* At this point we have a = d in assumption and
      ~ P a d /\ ~ P d a \/ P a d \/ a = d \/ P d a in goal.
    I think a = d should mean that either they are equal_rank or a = d and
    this should be used to discharge the goal *)
  right. firstorder.
  exists f.  split; intros. rewrite e in Hc, Hd.
  pose proof (H c d0). simpl in *. firstorder.
  rewrite e in Hc, Hd.
  pose proof (H c d0). simpl in *. firstorder.

  (* a <> d *)
  split. apply in_eq.
  split. pose proof (H a d (in_eq a l)). firstorder.
  split.  admit.
  (* At this point we a <> d in assumption and
       ~ P a d /\ ~ P d a \/ P a d \/ a = d \/ P d a in goal.
      I think a <> d should mean that either P a d or P d a and this
      should discharge the assumption
   *)
  exists f. split; intros. simpl in Hc, Hd. destruct (A_dec d a).
  symmetry in e. pose proof (n e). inversion H1.
  simpl in *. destruct Hc, Hd.  firstorder.
  pose proof (H c d0). firstorder.
  pose proof (H c d0). firstorder.
  pose proof (H c d0). firstorder.
  pose proof (H c d0). firstorder.

  (* reverse direction *)
  destruct H as [x H]. Check fold_left.
  pose proof (H x). destruct H0 as [H1 [H2 [H3 [f H4]]]].

  induction l. firstorder.

  (* either a = c or a <> c *)


  Lemma dec_now : forall (P : A -> A -> Prop),
      (forall c d, P c d \/ ~P c d) ->
      {valid P} + {~valid P}.
  Proof.
    intros P H. unfold valid.
