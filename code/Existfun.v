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
Require Import ListLemma.*) 
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

Theorem transitive_dec :
  forall (A : Type) (Hcd : forall (c d : A), {c = d} + {c <> d})
         (P : A -> A -> Prop) (Hp : forall (c d : A), {P c d} + {~P c d}) (l : list A),
    {forall x y z, In x l -> In y l -> In z l -> P x y -> P y z -> P x z} +
    {~(forall x y z, In x l -> In y l -> In z l -> P x y -> P y z -> P x z)}.
Proof.
  intros A Hcd P Hp.
  induction l.
  left; firstorder.

  destruct IHl. Admitted.

  
  
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


  Fixpoint listmax (f : A -> nat) (l : list A) : nat :=
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

   
  
  (* Hold this for moment *)
  
  Lemma validity_after_remove_cand :
    forall (l : list A) (a0 : A),
      vl (a0 :: l) <->
      vl l /\ ~P a0 a0 /\
      (forall (c d e : A), In c (a0 :: l) -> In d (a0 :: l) -> In e (a0 :: l) ->
                           P c d -> P d e -> P c e) /\
      (forall (c e : A), In c l -> In e l ->  P c a0 -> P a0 e -> P c e) /\
      ((exists (a0' : A), In a0' l /\ forall (x : A), In x l -> (P a0 x <-> P a0' x) /\
                                                                (P x a0 <-> P x a0')) \/
       (* forall (x : A), In x l -> P x a0 \/ P a0 x *)
       (forall (x : A), In x l -> (P x a0 /\ ~P a0 x)
                                  \/ (P a0 x /\  ~P x a0))).
  Proof.
    unfold vl; split; intros.
    destruct H as [f H].
    split.
    exists f. firstorder.

    split. unfold not. intros. pose proof (proj1 (H a0 a0 (in_eq a0 l) (in_eq a0 l)) H0).
    omega.
    split. intros.
    pose proof (H c d H0 H1).
    pose proof (H d e H1 H2).
    firstorder.
    
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

    destruct H as [[f H1] [Ht [Hcd [Ht1 [[a [H2 H3]] | H2]]]]].
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


    rewrite <- Heqf1 in H4. rewrite <- Heql1 in H4.
    pose proof (listmax_upperbound l1 d f H8). omega.
    firstorder. firstorder. firstorder.

    (* In c l and d = a0 *)
    rewrite <- H3 in H4. rewrite <- H3.
    destruct (Adec c a0).
    rewrite e in H0.
    pose proof (H2 a0 H0). firstorder.
    destruct (Pdec a0 c).
    destruct (in_dec Adec c l).
    destruct (Adec a0 a0). simpl in H4.
    rewrite <- Heqf1 in H4. rewrite <- Heql1 in H4.
    apply lt_S_n in H4.
    clear n. clear i. clear e.
    pose proof (H2 c H0). destruct H6. firstorder.
    destruct H6. clear p.
    pose proof (H5 A _ _ c  H  H0).
    apply in_app_iff in H8. destruct H8.
    firstorder.
    
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
    apply Nat.lt_succ_l in H4. 

    clear H. clear H5. clear  Ht2. clear Heql1.
    assert (Ht6 : listmax f l1 < f c).
    induction l1. inversion H4.
    assert (Hm : {f a >= listmax f l1} + {f a < listmax f l1}).
    pose proof (lt_eq_lt_dec (f a) (listmax f l1)) as H11.
    destruct H11 as [[H11 | H11] | H11]. right. auto.
    left. omega. left. omega.

    assert (Ht7 : listmax f (a :: l1) = max (f a) (listmax f l1)).
    simpl. destruct l1. simpl.
    rewrite Max.max_0_r. auto. auto.
    
    rewrite Ht7. rewrite Ht7 in H4. clear Ht7.
    destruct Hm.
    rewrite max_l.  pose proof (Ht5 a (in_eq a l1) c H8). omega.
    omega.
    rewrite max_r. rewrite max_r in H4.
    apply IHl1. omega. firstorder. omega. omega.
    omega. congruence. congruence. firstorder.

    (* In c l and In d l *)

    assert (Ht5: forall x, In x l1 -> forall y, In y l2 -> f x < f y).
    intros. apply H1.
    apply Permutation_sym in H.
    pose proof (H5 A (l1 ++ l2) l x H). apply H8.
    firstorder.
    apply Permutation_sym in H.
    pose proof (H5 A (l1 ++ l2) l y H). apply H8.
    firstorder.
    apply Ht1.
    apply Permutation_sym in H.
    pose proof (H5 A (l1 ++ l2) l x H). apply H8.
    firstorder.
    apply Permutation_sym in H.
    pose proof (H5 A (l1 ++ l2) l y H). apply H8.
    firstorder. firstorder. firstorder.



    destruct (Adec c a0).
    rewrite e in H0. pose proof (H2 a0 H0).
    firstorder.

    destruct (Pdec a0 c).
    destruct (in_dec Adec c l).
    destruct (Adec d a0).
    rewrite e in H3. pose proof (H2 a0 H3).
    firstorder.
    destruct (Pdec a0 d). destruct (in_dec Adec d l).
    simpl in H4. apply H1; auto. omega.
    firstorder. simpl in H4.

    clear n. clear i. clear n0.
    pose proof (H2 c H0). destruct H6. firstorder.
    clear p. destruct H6.
    pose proof (H2 d H3). destruct H8. destruct H8.
    clear n1.
    pose proof (H5 A l (l1 ++ l2) c H H0).
    pose proof (H5 A l (l1 ++ l2) d H H3).
    apply in_app_iff in H10. destruct H10.
    pose proof (Ht2 c H10). firstorder.
    apply in_app_iff in H11. destruct H11.
    pose proof (Ht5 d H11 c H10). omega.


    firstorder. firstorder.
    firstorder. simpl in H4.
    destruct (Adec d a0).
    rewrite e in H3. pose proof (H2 a0 H3). firstorder.
    destruct (Pdec a0 d). destruct (in_dec Adec d l).
    simpl in H4. firstorder.
    firstorder. destruct (in_dec Adec d l).
    simpl in H4. firstorder. firstorder.
    (* proof finished  :) *)
  Qed.

  Definition phi a l :=
    ((exists a0' : A, In a0' l /\
                      (forall x : A, In x l -> (P a x <-> P a0' x) /\
                                               (P x a <-> P x a0')))
     \/
     (forall x : A, In x l -> P x a /\ ~ P a x \/ P a x /\ ~ P x a)).
                       
  Lemma phi_decidable :
    forall a l, vl l -> {phi a l} + {~(phi a l)}. 
  Proof.
    intros a l Hv.
    unfold vl in Hv.
    Admitted.

    
  (* This Lemma is from ListLemma. Move all the lemma into ListLemma.v later *)
  Lemma not_equal_elem : forall (A : Type) (a x : A) (l : list A),
      In a l -> ~ In x l -> x <> a.
  Proof.
    intros A0 a x l H1 H2.
    induction l. inversion H1.
    specialize (proj1 (not_in_cons x a0 l) H2); intros.
    simpl in H1. destruct H as [H3 H4]. destruct H1.
    subst. assumption. apply IHl. assumption. assumption.
  Qed.
  
  Lemma not_in_list : forall (a : A) (l : list A) (f : A -> nat),
      ~In (f a) (map f l) -> (forall x, In x l -> f a <> f x).  
  Proof.
    intros a l f Hnin x Hx.
    pose proof (in_map f l x Hx).
    pose proof (not_equal_elem _ (f x) (f a) (map f l)  H Hnin).
    auto.
  Qed.
  
    (* This proof is mostly followed by validity_after_remove_cand. *)
  Lemma vl_or_notvl : forall l : list A, vl l + ~vl l.
  Proof. 
    
    intros l. 
    induction l.
    left. unfold vl.
    exists (fun x => 0).
    intros c d Hc Hd; inversion Hc. 
 
    destruct IHl.
    pose proof (validity_after_remove_cand l a).
    pose proof (Pdec a a).
    destruct H0.
    right. firstorder.
    pose proof (transitive_dec A Adec P Pdec (a :: l)).
    destruct H0. 

    pose proof (phi_decidable a l v). 
    destruct H0. unfold phi in p0.
    
    
    left. apply H.  split. auto.
    split. auto. split. auto.
    split. auto. intros.
    pose proof (p c a e (or_intror H0) (in_eq a l) (or_intror H1) H2 H3).
    auto. assumption.
  
    right. unfold phi in n0.
    unfold vl. unfold not.
    intros. apply n0. clear n0.
    destruct H0 as [f Hv].

    assert (Hnat : forall x y : nat, {x = y} + {x <> y}) by (auto with arith).
    
    pose proof (in_dec Hnat (f a) (map f l)).  clear Hnat.
    destruct H0.
    apply in_map_iff in i. destruct i as [x [Hl Hr]].

    left.  exists x. split. auto.
    intros. split. split; intros. 
    pose proof (Hv a x0 (in_eq a l) (or_intror H0)).
    pose proof ((proj1 H2) H1). rewrite <- Hl in H3.
    pose proof (proj2 (Hv x x0 (or_intror Hr) (or_intror H0)) H3).
    auto. 
    pose proof (Hv x x0 (or_intror Hr) (or_intror H0)).
    pose proof (proj1 H2 H1).
    rewrite Hl in H3.
    pose proof (proj2 (Hv a x0 (in_eq a l) (or_intror H0)) H3). auto.

    split; intros.
    pose proof (Hv x0 a (or_intror H0) (in_eq a l)).
    firstorder.

    pose proof (Hv x0 x (or_intror H0) (or_intror Hr)).
    firstorder. 

    (* go right *)
    right. intros x Hx.
    remember a as a0.
    destruct (lt_eq_lt_dec (f a0) (f x)) as [[H1 | H1] | H1].
    pose proof (Hv a0 x (in_eq a0 l) (or_intror Hx)).
    right. split. firstorder. firstorder.
    (* this case is not possible because f a0 in not in the list *)
    pose proof (not_in_list a0 l f n0 x Hx). omega.

    pose proof (Hv x a0 (or_intror Hx) (in_eq a0 l)).
    firstorder.
    
    right. unfold vl.
    unfold not. intros. apply n0.
    intros. destruct H0 as [f Hv]. clear n0.
    pose proof (proj1 (Hv x y H1 H2) H4).
    pose proof (proj1 (Hv y z H2 H3) H5).
    apply Hv. auto. auto. omega.
    
    right. firstorder.
  Qed.
  

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
    pose proof (vl_or_notvl l).
    pose proof (from_vl_to_valid l Hin).
    destruct H.
    left. pose proof (proj2 H0 v). assumption.
    right. unfold not. intros.
    apply n. clear n.
    pose proof (proj1 H0 H). assumption.
  Qed.
  
End Cand.

