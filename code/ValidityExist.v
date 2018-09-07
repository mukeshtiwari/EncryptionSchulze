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
Require Import Coq.ZArith.ZArith.
Require Import ListLemma.
Require Import Psatz.               
Require Import Coq.Logic.Decidable.
Import ListNotations.

Notation "'existsT' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'existsT' '/ ' x .. y , '/ ' p ']'") : type_scope.

Section Cand.
  Variable A : Type.
  Variable P : A -> A -> Z.
  Hypothesis Adec : forall (c d : A), {c = d} + {c <> d}.
  (* Our matrix is -1, 0, or 1 *)
  Hypothesis Pdec : forall (c d : A), {P c d = -1} + {P c d = 0} + {P c d = 1}.

  
  (* A is finite. finite : Type -> Type *)
  Definition finite := existsT (l : list A), forall (a : A), In a l.

  
  (* vl : forall A : Type, (P : A -> A -> Z) -> (list A) -> Prop *)
  Definition vl (l : list A) :=
    exists (f : A -> nat), forall (c d : A),
        In c l -> In d l ->
        ((P c d = 1 <-> (f c < f d)%nat) /\
         (P c d = 0 <-> (f c = f d)%nat) /\
         (P c d = -1 <-> (f c > f d)%nat)).

  
  Fixpoint listmax (f : A -> nat) (l : list A) : nat :=
    match l with
    | [] => O
    | [h] => f h
    | h :: t => max (f h) (listmax f t)
    end.


  Lemma listmax_upperbound :
    forall (l : list A) (d : A) (f : A -> nat) (Hin : In d l),
      (f d <= listmax f l)%nat.
  Proof.
    induction l.
    intros. inversion Hin.

    intros d f Hin.
    assert (Hm : {(f a >= listmax f l)%nat} + {(f a < listmax f l)%nat}).
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
      vl l /\ P a0 a0 = 0 /\
      (forall (c d e : A), In c (a0 :: l) -> In d (a0 :: l) -> In e (a0 :: l) ->
                      (P c d = 1 -> P d e = 1 -> P c e = 1) /\
                      (P c d = 1 -> P d e = 0 -> P c e = 1) /\
                      (P c d = 0 -> P d e = 1 -> P c e = 1) /\
                      (P c d = 0 -> P d e = 0 -> P c e = 0) /\
                      (P c d = 0 -> P d e = -1 -> P c e = -1) /\
                      (P c d = -1 -> P d e = 0 -> P c e = -1) /\
                      (P c d = -1 -> P d e = -1 -> P c e = -1)) /\
      (forall (c e : A), In c l -> In e l ->
                    (P c a0 = 1 -> P a0 e = 1 -> P c e = 1) /\
                    (P c a0 = 1 -> P a0 e = 0 -> P c e = 1) /\
                    (P c a0 = 0 -> P a0 e = 1 -> P c e = 1) /\
                    (P c a0 = 0 -> P a0 e = 0 -> P c e = 0) /\
                    (P c a0 = 0 -> P a0 e = -1 -> P c e = -1) /\
                    (P c a0 = -1 -> P a0 e = 0 -> P c e = -1) /\
                    (P c a0 = -1 -> P a0 e = -1 -> P c e = -1)) /\
      ((exists (a0' : A), In a0' l /\ forall (x : A), In x l ->
                                           (P a0 x = P a0' x) /\
                                           (P x a0 = P x a0')) \/
       (forall (x : A), In x l -> (P x a0 = 1 /\ P a0 x = -1)
                            \/ (P a0 x = 1 /\ P x a0 = -1))).
   Proof. 
     unfold vl; split; intros.
     destruct H as [f H].
     split.
     exists f.  intros. 
     specialize (H c d (or_intror H0) (or_intror H1)).
     assumption.
     (* P a0 a0 *)
     split.
     specialize (H a0 a0 (in_eq a0 l) (in_eq a0 l)).
     destruct H as [H1 [H2 H3]].
     specialize ((proj2 H2) eq_refl). intros. assumption.


     repeat (split; intros).
     pose proof (H c d H0 H1).
     pose proof (H d e H1 H2).
     destruct H5 as [H5 [H7 H8]].
     destruct H6 as [H6 [H9 H10]].
     specialize ((proj1 H5) H3); intros.
     specialize ((proj1 H6) H4); intros.
     assert (f c < f e)%nat by lia.
     pose proof (H c e H0 H2). destruct H14.
     apply H14. assumption.

     
     pose proof (H c d H0 H1).
     pose proof (H d e H1 H2).
     destruct H5 as [H5 [H7 H8]].
     destruct H6 as [H6 [H9 H10]]. 
     specialize ((proj1 H5) H3); intros.
     specialize ((proj1 H9) H4); intros.
     assert (f c < f e)%nat by lia.
     pose proof (H c e H0 H2). destruct H14.
     apply H14.  assumption.

     (* Learn bloody LTac *)

     pose proof (H c d H0 H1).
     pose proof (H d e H1 H2).
     destruct H5 as [H5 [H7 H8]].
     destruct H6 as [H6 [H9 H10]].
     specialize ((proj1 H7) H3); intros.
     specialize ((proj1 H6) H4); intros.
     assert (f c < f e)%nat by lia.
     pose proof (H c e H0 H2). destruct H14.
     apply H14. assumption.

    
     
     pose proof (H c d H0 H1).
     pose proof (H d e H1 H2).
     destruct H5 as [H5 [H7 H8]].
     destruct H6 as [H6 [H9 H10]].
     apply H7 in H3. apply H9 in H4.
     rewrite H4 in H3.
     pose proof (H c e H0 H2).
     destruct H11. destruct H12. apply H12.
     assumption.


     pose proof (H c d H0 H1).
     pose proof (H d e H1 H2).
     destruct H5 as [H5 [H7 H8]].
     destruct H6 as [H6 [H9 H10]].
     apply H7 in H3. apply H10 in H4.
     assert (f c  > f e)%nat by lia.
     pose proof (H c e H0 H2).
     destruct H12.  destruct H13. apply H14.
     assumption.

     pose proof (H c d H0 H1).
     pose proof (H d e H1 H2).
     destruct H5 as [H5 [H7 H8]].
     destruct H6 as [H6 [H9 H10]].
     apply H8 in H3. apply H9 in H4.
     assert (f c  > f e)%nat by lia.
     pose proof (H c e H0 H2).
     destruct H12.  destruct H13. apply H14.
     assumption.

     pose proof (H c d H0 H1).
     pose proof (H d e H1 H2).
     destruct H5 as [H5 [H7 H8]].
     destruct H6 as [H6 [H9 H10]].
     apply H8 in H3. apply H10 in H4.
     assert (f c  > f e)%nat by lia.
     pose proof (H c e H0 H2).
     destruct H12.  destruct H13. apply H14.
     assumption.

     pose proof (H c a0 (in_cons _ c l H0) (in_eq a0 l)).
     pose proof (H a0 e (in_eq a0 l) (in_cons _ e l H1)).
     destruct H4 as [H6 [H7 H8]].
     destruct H5 as [H9 [H10 H11]].
     apply H6 in H2. apply H9 in H3.
     assert (f c < f e)%nat by lia.
     pose proof (H c e (or_intror H0) (or_intror H1)).
     destruct H5. destruct H12.
     apply H5. assumption.

     pose proof (H c a0 (in_cons _ c l H0) (in_eq a0 l)).
     pose proof (H a0 e (in_eq a0 l) (in_cons _ e l H1)).
     destruct H4 as [H6 [H7 H8]].
     destruct H5 as [H9 [H10 H11]].
     apply H6 in H2. apply H10 in H3.
     assert (f c < f e)%nat by lia.
     pose proof (H c e (or_intror H0) (or_intror H1)).
     destruct H5. destruct H12.
     apply H5. assumption.



     pose proof (H c a0 (in_cons _ c l H0) (in_eq a0 l)).
     pose proof (H a0 e (in_eq a0 l) (in_cons _ e l H1)).
     destruct H4 as [H6 [H7 H8]].
     destruct H5 as [H9 [H10 H11]].
     apply H7 in H2. apply H9 in H3.
     assert (f c < f e)%nat by lia.
     pose proof (H c e (or_intror H0) (or_intror H1)).
     destruct H5. destruct H12.
     apply H5. assumption.

     pose proof (H c a0 (in_cons _ c l H0) (in_eq a0 l)).
     pose proof (H a0 e (in_eq a0 l) (in_cons _ e l H1)).
     destruct H4 as [H6 [H7 H8]].
     destruct H5 as [H9 [H10 H11]].
     apply H7 in H2. apply H10 in H3.
     assert (f c = f e)%nat by lia.
     pose proof (H c e (or_intror H0) (or_intror H1)).
     destruct H5. destruct H12.
     apply H12. assumption.


     pose proof (H c a0 (in_cons _ c l H0) (in_eq a0 l)).
     pose proof (H a0 e (in_eq a0 l) (in_cons _ e l H1)).
     destruct H4 as [H6 [H7 H8]].
     destruct H5 as [H9 [H10 H11]].
     apply H7 in H2. apply H11 in H3.
     assert (f c > f e)%nat by lia.
     pose proof (H c e (or_intror H0) (or_intror H1)).
     destruct H5. destruct H12.
     apply H13. assumption.


     pose proof (H c a0 (in_cons _ c l H0) (in_eq a0 l)).
     pose proof (H a0 e (in_eq a0 l) (in_cons _ e l H1)).
     destruct H4 as [H6 [H7 H8]].
     destruct H5 as [H9 [H10 H11]].
     apply H8 in H2. apply H10 in H3.
     assert (f c > f e)%nat by lia.
     pose proof (H c e (or_intror H0) (or_intror H1)).
     destruct H5. destruct H12.
     apply H13. assumption.


     pose proof (H c a0 (in_cons _ c l H0) (in_eq a0 l)).
     pose proof (H a0 e (in_eq a0 l) (in_cons _ e l H1)).
     destruct H4 as [H6 [H7 H8]].
     destruct H5 as [H9 [H10 H11]].
     apply H8 in H2. apply H11 in H3.
     assert (f c > f e)%nat by lia.
     pose proof (H c e (or_intror H0) (or_intror H1)).
     destruct H5. destruct H12.
     apply H13. assumption.


     assert (Hnat : forall x y : nat, {x = y} + {x <> y}) by (auto with arith).
     pose proof (in_dec Hnat (f a0) (map f l)).  clear Hnat.
     destruct H0.
     apply in_map_iff in i. destruct i as [a [Hl Hr]].
     (* I know the exitence of element which is in l and equal to f a0 *)
     left. exists a. split. assumption.
     intros x Hx. split.


     pose proof (H a0 x (in_eq a0 l) (or_intror Hx)).
     pose proof (H a x (or_intror Hr) (or_intror Hx)).
     destruct H0 as [[H2 H3] [[H5 H6] [H7 H8]]].
     destruct H1 as [[H9 H10] [[H11 H12] [H13 H14]]].
     pose proof (lt_eq_lt_dec (f a) (f x)).
     destruct H0. destruct s.
     pose proof (H10 l0). rewrite Hl in l0.
     pose proof (H3 l0). rewrite H0. rewrite H1. auto.
     pose proof (H12 e). rewrite Hl in e.
     pose proof (H6 e). rewrite H0, H1. auto.
     assert (f a > f x)%nat by lia.
     pose proof (H14 H0). rewrite Hl in H0.
     pose proof (H8 H0). rewrite H1, H4. auto.

     pose proof (H x a0 (or_intror Hx) (in_eq a0 l)).
     pose proof (H x a (or_intror Hx) (or_intror Hr)).
     destruct H0 as [[H2 H3] [[H5 H6] [H7 H8]]].
     destruct H1 as [[H9 H10] [[H11 H12] [H13 H14]]].
     pose proof (lt_eq_lt_dec (f a) (f x)).
     destruct H0. destruct s.
     assert (f x > f a)%nat by lia.
     pose proof (H14 H0). rewrite Hl in H0.
     pose proof (H8 H0). rewrite H1, H4. auto.
     assert (f x = f a)%nat by lia.
     pose proof (H12 H0). rewrite Hl in H0.
     pose proof (H6 H0). rewrite H1, H4. auto.
     pose proof (H10 l0). rewrite Hl in l0.
     pose proof (H3 l0). rewrite H0, H1. auto.

     (* time to go right *)
     right. intros x Hx.
     destruct (lt_eq_lt_dec (f a0) (f x)) as [[H1 | H1] | H1].
     pose proof (H a0 x (in_eq a0 l) (or_intror Hx)).
     right. split. firstorder. firstorder.

     (* f 0 can not be equal to f x *)
     unfold not in n. assert False. apply n.
     rewrite H1. Check in_map.
     pose proof (in_map f l x Hx). assumption.
     inversion H0.

     pose proof (H x a0 (or_intror Hx) (in_eq a0 l)).
     firstorder.
     
     (* finished first half of the proof *) 
     
     destruct H as [[f H1] [Ht [Hcd [Ht1 [[a [H2 H3]] | H2]]]]].  
     (* from H3 I know that f a = f a0  so I am going to supply same function  *)
     exists (fun c => if Adec c a0 then f a else f c). intros c d H4 H5. destruct H4, H5.  

     subst. firstorder.
     split.
     split; intros.
     subst. destruct (Adec c c); destruct (Adec d c); try congruence.
     pose proof (H3 d H0).
     destruct H. clear H5.
     assert (P a d = 1) by lia.
     pose proof (H1 a d H2 H0). firstorder.

     subst. destruct (Adec c c); destruct (Adec d c);
              try congruence; try lia.
     pose proof (H1 a d H2 H0). firstorder.

     split.
     split; intros.
     subst. destruct (Adec c c); destruct (Adec d c);
              try congruence; try lia.
     pose proof (H3 d H0). assert (P a d = 0) by lia.
     pose proof (H1 a d H2 H0).  firstorder.
     subst. destruct (Adec c c); destruct (Adec d c);
              try congruence; try lia.
     pose proof (H1 a d H2 H0).
     pose proof (H3 d H0).
     destruct H. destruct H6. apply H6 in H4.
     destruct H5. rewrite H4 in H5.  assumption.

     split; intros.
     subst. destruct (Adec c c); destruct (Adec d c);
              try congruence; try lia.
     pose proof (H3 d H0).
     pose proof (H1 a d H2 H0).
     assert (P a d = -1) by lia. firstorder.
     subst. destruct (Adec c c); destruct (Adec d c);
              try congruence; try lia.
     pose proof (H3 d H0).
     pose proof (H1 a d H2 H0).
     destruct H5. 
     destruct H6. apply H7 in H4.
     assert (P c d = -1) by lia.
     assumption.

     split.
     split; intros.
     subst. destruct (Adec c d); destruct (Adec d d);
              try congruence; try lia.
     pose proof (H3 c H). assert (P c a = 1) by lia.
     pose proof (H1 c a H H2). firstorder.
     subst. destruct (Adec c d); destruct (Adec d d);
              try congruence; try lia.
     pose proof (H3 c H).
     pose proof (H1 c a H H2).
     destruct H5. destruct H6.
     apply H5 in H4. destruct H0.
     rewrite H4 in H8. assumption.

     split.
     split; intros.
     subst. destruct (Adec c d); destruct (Adec d d); try congruence;
              try lia.
     pose proof (H3 c H).
     assert (P c a = 0) by lia.
     pose proof (H1 c a H H2). firstorder.
     subst. destruct (Adec c d); destruct (Adec d d);
              try congruence; try lia.
     pose proof (H3 c H). destruct H0.
     pose proof (H1 c a H H2). destruct H6.
     destruct H7. apply H7 in H4. rewrite H4 in H5.
     assumption.

     split; intros.
     subst. destruct (Adec c d); destruct (Adec d d); try congruence;
              try lia.
     pose proof (H3 c H).
     assert (P c a = -1) by lia.
     pose proof (H1 c a H H2). firstorder.
     subst. destruct (Adec c d); destruct (Adec d d);
              try congruence; try lia.
     pose proof (H3 c H). destruct H0.
     pose proof (H1 c a H H2). destruct H6.
     destruct H7. apply H8 in H4. rewrite H4 in H5.
     assumption.


     split. 
     split; intros. 
     subst. destruct (Adec c a0); destruct (Adec d a0); try congruence;
              try lia.
     subst. pose proof (H3 d H0).
     destruct H5. assert (P a d = 1) by lia.
     pose proof (H1 a d H2 H0).
     destruct H8. apply H8. assumption.
     subst. pose proof (H3 c H).
     destruct H5. assert (P c a = 1) by lia.
     pose proof (H1 c a H H2). destruct H8.
     apply H8. assumption.

     pose proof (H1 c d H H0). firstorder.
     destruct (Adec c a0); destruct (Adec d a0);
       try congruence; try lia.
     subst.
     pose proof (H1 a d H2 H0).
     pose proof (H3 d H0). destruct H6.
     destruct H5. destruct H8. apply H5 in H4.
     rewrite H4 in H6. assumption.

     subst. pose proof (H1 c a H H2).
     destruct H5. apply H5 in H4.
     pose proof (H3 c H). assert (P c a0 = 1) by lia.
     assumption.

     pose proof (H1 c d H H0). destruct H5.
     apply H5. assumption.


     split.
     split; intros.
     destruct (Adec c a0); destruct (Adec d a0);
       try congruence; try lia.
     subst. pose proof (H3 d H0).
     destruct H5. pose proof (H1 a d H2 H0).
     destruct H7. destruct H8. apply H8.
     rewrite H4 in H5. congruence.

     subst. pose proof (H3 c H).
     destruct H5.
     pose proof (H1 c a H H2).
     destruct H7. destruct H8.
     apply H8. rewrite H4 in H6.
     congruence.

     pose proof (H1 c d H H0). destruct H5.
     destruct H6. apply H6. assumption.
     destruct (Adec c a0); destruct (Adec d a0);
       try congruence; try lia.
     subst. pose proof (H3 d H0).
     destruct H5. pose proof (H1 a d H2 H0).
     destruct H7. destruct H8.
     apply H8 in H4. rewrite H4 in H5.
     assumption.

     subst. pose proof (H3 c H).
     destruct H5. pose proof (H1 c a H H2).
     destruct H7. destruct H8.
     apply H8 in H4. rewrite H4 in H6.
     assumption.

     pose proof (H1 c d H H0).
     destruct H5. destruct H6.
     apply H6. assumption.

     split; intros.
     destruct (Adec c a0); destruct (Adec d a0);
       try congruence; try lia.
     subst. pose proof (H3 d H0).
     destruct H5. pose proof (H1 a d H2 H0).
     destruct H7. destruct H8. apply H9.
     rewrite H4 in H5. congruence.

     subst. pose proof (H3 c H).
     destruct H5. pose proof (H1 c a H H2).
     destruct H7. destruct H8.
     apply H9. rewrite H4 in H6. congruence.

     pose proof (H1 c d H H0). destruct H5.
     destruct H6. apply H7. assumption.

     destruct (Adec c a0); destruct (Adec d a0);
       try congruence; try lia.
     subst. pose proof (H3 d H0).
     destruct H5. pose proof (H1 a d H2 H0).
     destruct H7. destruct H8.
     apply H9 in H4. rewrite H4 in H5. assumption.

     subst. pose proof (H1 c a H H2).
     destruct H5. destruct H6.
     pose proof (H3 c H). destruct H8.
     apply H7 in H4. rewrite H4 in H9.
     assumption.

     pose proof (H1 c d H H0). destruct H5.
     destruct H6. apply H7. assumption. 

     (* finished equivalent function *)

     (* filter all elements which are more preffered over a0 in l *)
     remember (filter (fun x => if P x a0 =? 1 then true else false) l) as l1.
     (* filter all elements for which a0 is preferred *)
     remember (filter (fun x => if P a0 x =? 1 then true else false) l) as l2.
     assert (Ht2 : forall x, In x l1 -> P x a0 = 1 /\ P a0 x = -1).
     intros. rewrite Heql1 in H.
     pose proof (proj1 (filter_In _ _ _) H).
     destruct H0.  pose proof (H2 x H0).
     destruct H4. auto.  destruct H4. rewrite H5 in H3.
     simpl in H3. inversion H3.

     assert (Ht3 : forall x, In x l2 -> P a0 x = 1 /\ P x a0 = -1).
     intros. rewrite Heql2 in H.
     pose proof (proj1 (filter_In _ _ _) H).
     destruct H0. pose proof (H2 x H0). destruct H4.
     destruct H4. rewrite H5 in H3. simpl in H3. inversion H3.
     auto.

     remember (fun x => if P x a0 =? 1 then true else false) as f1.
     remember (fun x => if P a0 x =? 1 then true else false) as g1.
     assert (Ht4 : forall x, In x l -> f1 x = negb (g1 x)).
     intros. rewrite Heqf1. rewrite Heqg1.
     pose proof (H2 x H). destruct H0.
     destruct H0. rewrite H0. rewrite H3.
     simpl. auto.
     destruct H0. rewrite H3. rewrite H0.
     simpl. auto. 
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
                     (listmax f (filter (fun y => if P y a0 =? 1 then true else false) l))
              | right _ =>
                if andb (if P a0 x =? 1 then true else false)
                        (if (in_dec Adec x l) then true else false)
                then plus (S (S O)) (f x)
                else  (f x)
              end). 
 
     split.
     split; intros.
     destruct H0, H3.
     subst. 
     (* c = a0 and d = a0 *)
     congruence. 
 
     (* c = a0 and In d l *)
     rewrite <- H0. rewrite <- H0 in H4.
     destruct (Adec a0 a0).
     destruct (Adec d a0). congruence.
     rewrite H4. simpl.
     destruct (in_dec Adec d l).
     simpl. apply lt_n_S.
 
     clear e.  clear i. clear n.
     pose proof Permutation_in. 
     pose proof (H5 A l (l1 ++ l2) d H H3).
     apply in_app_iff in H6. destruct H6.
     pose proof (Ht2 d H6). firstorder.
     rewrite <- Heqf1.
     rewrite <- Heql1.
  
     assert (Ht5: forall x, In x l1 -> forall y, In y l2 -> (f x < f y)%nat).
     intros. apply H1.
     apply Permutation_sym in H. 
     pose proof (H5 A (l1 ++ l2) l y H). apply H9.
     firstorder.
     apply Permutation_sym in H.
     pose proof (H5 A (l1 ++ l2) l x H). apply H9.
     firstorder.
     apply Ht1.
     apply Permutation_sym in H.
     pose proof (H5 A (l1 ++ l2) l y H). apply H9.
     firstorder.
     apply Permutation_sym in H.
     pose proof (H5 A (l1 ++ l2) l x H). apply H9.
     firstorder. firstorder. firstorder.
  
     clear H. clear H5. clear Heql1. clear Ht2.
     induction l1. simpl. omega.
     simpl. destruct l1. 
     pose proof (Ht5 a (in_eq a []) d H6). omega.
     apply Nat.max_lub_lt_iff. split.
     pose proof (Ht5 a (in_eq a (a1 :: l1)) d H6).
     omega. apply IHl1. firstorder.
     congruence. congruence.

     (* In c l and d = a0 *) 
     rewrite <- H3. rewrite <- H3 in H4.
     destruct (Adec c a0). destruct (Adec a0 a0).
     congruence. congruence. 

     pose proof (H2 c H0). destruct H5. destruct H5.
     rewrite H6. simpl. destruct (Adec a0 a0).
     simpl.
     clear n. clear e. 
     pose proof Permutation_in. pose proof (H7 A l (l1 ++ l2) c H H0).
     apply in_app_iff in H8. destruct H8.
     pose proof (Ht2 c H8).
     rewrite <- Heqf1.
     rewrite <- Heql1.

     clear H. clear Heql1. clear Ht2. clear H5.
     induction l1.
     inversion H8.
      
     simpl. destruct l1.
     destruct H8. rewrite H. omega. inversion H.
     pose proof (Max.max_dec (f a) (listmax f (a1 :: l1))).
     destruct H as [H | H].
     rewrite H.
     destruct H8. rewrite H5. omega.
     pose proof (IHl1 H5).
     apply Nat.max_l_iff in H. omega.
     rewrite H. destruct H8.
     rewrite <- H5.
     apply Nat.max_r_iff in H. omega.
     pose proof (IHl1 H5). assumption.
     firstorder. congruence.
     destruct H5. rewrite H5. simpl.
     destruct (Adec a0 a0). congruence.
     rewrite Ht. simpl. rewrite H4 in H6. inversion H6.
 
     (* In c l and In d l *)
     destruct (Adec c a0).
     destruct (Adec d a0).
     congruence. rewrite e in H0.
     pose proof (H2 a0 H0). firstorder.
     simpl. 
     pose proof (H2 c H0) as Htt.
     destruct Htt as [[Htt1 Htt2] | [Htt1 Htt2]].
     rewrite Htt2. simpl.
     destruct (Adec d a0).
     rewrite e in H3.
     pose proof (H2 a0 H3). firstorder.
     pose proof (H2 d H3) as Ht5.
     destruct Ht5 as [[Ht5 Ht6] | [Ht5 Ht6]].
     rewrite Ht6. simpl. firstorder.
     rewrite Ht5. simpl. destruct (in_dec Adec d l).
 
     pose proof (H2 c H0).
     pose proof (H2 d H3).
     destruct H5, H6.
     destruct H5. destruct H6. firstorder.
     destruct H5. destruct H6.
     pose proof (Ht1 c d H0 H3).
     destruct H9. specialize (H9 H5 H6).
     pose proof (H1 c d H0 H3). destruct H11.
     apply H11 in H9. lia.
     destruct H5. destruct H6. firstorder.
     destruct H5. congruence. congruence.
     rewrite Htt1. simpl.
     destruct (in_dec Adec c l).
     destruct (Adec d a0).
     apply lt_n_S. rewrite e in H4. rewrite H4 in Htt2.
     congruence.
     assert ((if in_dec Adec d l then true else false) = true).
     destruct (in_dec Adec d l). auto. congruence.
     rewrite H5. clear H5. simpl.
     pose proof (H2 d H3). destruct H5.
     destruct H5. rewrite H6. simpl.
     pose proof (Ht1 c d H0 H3).
     destruct H7. destruct H8. destruct H9.
     destruct H10. destruct H11. destruct H12.
     specialize (H13 Htt2 H6). rewrite H13 in H4.
     lia.
     destruct H5. rewrite H5. simpl.
     repeat (apply lt_n_S).
     pose proof (H1 c d H0 H3).
     destruct H7. apply H7. assumption.
     congruence.
 
     pose proof Permutation_in as Hp.
     destruct H0, H3.
     (* c = a0 and d = a0 *)
     rewrite <- H0 in H4.
     rewrite <- H3 in H4.
     omega.

     (* c = a0 and In d l *)
     rewrite <- H0 in H4.
     destruct (Adec a0 a0).
     destruct (Adec d a0). omega.
     pose proof (H2 d H3). destruct H5.
     destruct H5. rewrite H6 in H4. simpl in H4.
     rewrite <- Heqf1 in H4.
     rewrite <- Heql1 in H4.
     rewrite <- H0.
     pose proof (listmax_upperbound l1 d f).
     rewrite Heqf1 in Heql1.
     pose proof (Hp _ _ _ d H H3).
     apply in_app_iff in H8. destruct H8.
     specialize (H7 H8). omega.
     firstorder.
     destruct H5. rewrite H5 in H4. simpl in H4.
     assert ((if in_dec Adec d l then true else false) = true).
     destruct (in_dec Adec d l). auto. congruence.
     rewrite H7 in H4. clear H7.
     rewrite <- H0. auto.
     congruence.

     (* In c l and d = a0 *)
     rewrite <- H3 in H4. rewrite <- H3.
     destruct (Adec c a0).
     rewrite e in H0.
     pose proof (H2 a0 H0). firstorder.
     pose proof (H2 c H0) as Ht5.
     destruct Ht5 as [[Ht5 Ht6] | [Ht5 Ht6]].
     auto. rewrite Ht5 in H4. simpl in H4.
     assert ((if in_dec Adec c l then true else false) = true).
     destruct (in_dec Adec c l). auto. congruence.
     rewrite H5 in H4. clear H5.
     destruct (Adec a0 a0). simpl in H4.
     rewrite <- Heqf1 in H4. rewrite <- Heql1 in H4.
     apply lt_S_n in H4.  clear n.  clear e.
     pose proof (Hp A l (l1 ++ l2) c H H0).
     apply in_app_iff in H5. destruct H5. firstorder.


     assert (Htt5: forall x, In x l1 -> forall y, In y l2 -> (f x < f y)%nat).
     intros. apply H1.
     apply Permutation_sym in H.
     pose proof (Hp A (l1 ++ l2) l y H). apply H8.
     firstorder.
     apply Permutation_sym in H.
     pose proof (Hp A (l1 ++ l2) l x H). apply H8.
     firstorder.
     apply Ht1.
     apply Permutation_sym in H.
     pose proof (Hp A (l1 ++ l2) l y H). apply H8.
     firstorder.
     apply Permutation_sym in H.
     pose proof (Hp A (l1 ++ l2) l x H). apply H8.
     firstorder. firstorder. firstorder.
     apply Nat.lt_succ_l in H4.

     clear Heql1. clear H. clear Ht2.
     assert (Htt6 : (listmax f l1 < f c)%nat).
     induction l1. inversion H4.
     assert (Hm : {(f a >= listmax f l1)%nat} + {(f a < listmax f l1)%nat}).
     pose proof (lt_eq_lt_dec (f a) (listmax f l1)) as H11.
     destruct H11 as [[H11 | H11] | H11]. right. auto.
     left. omega. left. omega.

     assert (Ht7 : listmax f (a :: l1) = max (f a) (listmax f l1)).
     simpl. destruct l1. simpl.
     rewrite Max.max_0_r. auto. auto.
 
     rewrite Ht7. rewrite Ht7 in H4. clear Ht7.
     destruct Hm.
     rewrite max_l.  pose proof (Htt5 a (in_eq a l1) c H5).
     omega. omega.
     rewrite max_r. rewrite max_r in H4.
     apply IHl1.  omega. firstorder. omega. omega.
     omega. congruence.
 
     (* In c l and In d l *)
     assert (Ht5: forall x, In x l1 -> forall y, In y l2 -> (f x < f y)%nat).
     intros. apply H1.
     apply Permutation_sym in H.
     pose proof (Hp A (l1 ++ l2) l y H). apply H7.
     firstorder.
     apply Permutation_sym in H.
     pose proof (Hp A (l1 ++ l2) l x H). apply H7.
     firstorder.
     apply Ht1.
     apply Permutation_sym in H.
     pose proof (Hp A (l1 ++ l2) l y H). apply H7.
     firstorder.
     apply Permutation_sym in H.
     pose proof (Hp A (l1 ++ l2) l x H). apply H7.
     firstorder. firstorder. firstorder.

     destruct (Adec c a0). 
     rewrite e in H0. pose proof (H2 a0 H0).
     firstorder.

     pose proof (H2 c H0). destruct H5 as [[Htt5 Htt6] | [Htt5 Htt6]].
     rewrite Htt6 in H4. simpl in H4.
     destruct (Adec d a0).  rewrite e in H3.
     firstorder.

     pose proof (H2 d H3). destruct H5 as [[Htt7 Htt8] | [Htt7 Htt8]].
     rewrite Htt8 in H4. simpl in H4.  firstorder.
     rewrite Htt7 in H4. simpl in H4.

     assert ((if in_dec Adec d l then true else false) = true).
     destruct (in_dec Adec d l). auto. congruence.
     rewrite H5 in H4. clear H5.
     pose proof (Ht1 c d H0 H3). firstorder.
     rewrite Htt5 in H4. simpl in H4.
     assert ((if in_dec Adec c l then true else false) = true).
     destruct (in_dec Adec c l). auto. congruence.
     rewrite H5 in H4. clear H5. destruct (Adec d a0).
     rewrite e in H3. firstorder.
     pose proof (H2 d H3). destruct H5 as [[Htt7 Htt8] | [Htt7 Htt8]].
     rewrite Htt8 in H4. simpl in H4.
     pose proof (Hp A l (l1 ++ l2) c H H0).
     pose proof (Hp A l (l1 ++ l2) d H H3).
     apply in_app_iff in H5. destruct H5.
     pose proof (Ht2 c H5). firstorder.
     apply in_app_iff in H6. destruct H6.
     pose proof (Ht5 d H6 c H5). omega.
     firstorder.  rewrite Htt7 in H4. simpl in H4.
     assert ((if in_dec Adec d l then true else false) = true).
     destruct (in_dec Adec d l). auto. congruence.
     rewrite H5 in H4. clear H5. 
     pose proof (H1 c d H0 H3). destruct H5. apply H5. omega.
 
     (* P c d = 0 *)

     split.
     split; intros.
     destruct H0; destruct H3.
 
     (* c = a0, d = a0 *)
     rewrite <- H0. rewrite <- H3.
     rewrite <- H0 in H4. rewrite <- H3 in H4.
     destruct (Adec a0 a0); try auto; try congruence.

     (*c = a0, In d l *)
     rewrite <- H0. rewrite <- H0 in H4.
     destruct (Adec a0 a0); destruct (Adec d a0);
       try auto; try congruence.
     pose proof (H2 d H3);
     destruct H5 as [[Ht5 Ht6] | [Ht5 Ht6]];
       try omega.

     (* In c l, d = a0 *)
     rewrite <- H3. rewrite <- H3 in H4.
     destruct (Adec c a0); destruct (Adec a0 a0);
       try auto; try congruence.
     pose proof (H2 c H0).
     destruct H5 as [[Ht5 Ht6] | [Ht5 Ht6]];
       try omega.

     (* In c l, In d l *)
     pose proof (H1 c d H0 H3).
     destruct H5 as [H6 [H7 H8]].
     destruct (Adec c a0); destruct (Adec d a0);
       try auto; try congruence.
     pose proof (H2 d H3). 
     destruct H5 as [[Ht5 Ht6] | [Ht5  Ht6]];
       try omega.
     rewrite Ht6. simpl.
     rewrite e in H0, H4, H8.
     omega.
     rewrite e in H4. omega.
     pose proof (H2 c H0).
     destruct H5 as [[Ht5 Ht6] | [Ht5 Ht6]];
       try auto; try omega.
     rewrite Ht6. simpl.
     rewrite e in H4. omega.
     rewrite Ht5. simpl.
     assert ((if in_dec Adec c l then true else false) = true).
     destruct (in_dec Adec c l). auto. congruence.
     rewrite H5. clear H5. rewrite e in H4. omega.
     (* P c d = 0 mean they are equally ranked. 
       P a0 c =? 1 -> P a0 d =? 1 and vice versa *)
     assert ((if in_dec Adec c l then true else false) = true).
     destruct (in_dec Adec c l). auto. congruence.
     rewrite H5. clear H5.
     assert ((if in_dec Adec d l then true else false) = true).
     destruct (in_dec Adec d l). auto. congruence.
     rewrite H5. clear H5.
     pose proof (H2 c H0). destruct H5 as [[Ht5 Ht6] | [Ht5 Ht6]];
                             try omega.  
     rewrite Ht6. simpl. 
     pose proof ((proj1 H7) H4).
     destruct (H2 d H3); try auto;
       try congruence.
     destruct H9 as [H9 H10].
     rewrite H10. simpl. auto.
     destruct H9. rewrite H9. simpl.
     pose proof (Ht1 c d H0 H3).
     destruct H11. specialize (H11 Ht5 H9).
     rewrite H4 in H11. inversion H11.

     rewrite Ht5. simpl.
     pose proof ((proj1 H7) H4).
     destruct (H2 d H3); try auto;
       try congruence.
     destruct H9 as [H9 H10].
     rewrite H10. simpl.
     pose proof (Ht1 d c H3 H0).
     destruct H11. specialize (H11 H9 Ht5).
     clear H12.
     pose proof (H1 d c H3 H0). destruct H12.
     apply H12 in H11.
     rewrite H5 in H11. omega. 
     destruct H9. rewrite H9. simpl. omega.


     pose proof Permutation_in as Hp.
     destruct H0; destruct H3; try auto;
       try congruence.
      
     (* c = a0, In d l *)
     rewrite <- H0. rewrite <- H0 in H4.
     destruct (Adec a0 a0); destruct (Adec d a0);
       try auto; try congruence.
     assert ((if in_dec Adec d l then true else false) = true).
     destruct (in_dec Adec d l). auto. congruence.
     rewrite H5 in H4. clear H5. rewrite andb_true_r in H4.
     destruct (H2 d H3); try omega.
     destruct H5 as [Ht5 Ht6].
     rewrite Ht6 in H4. simpl in *.

     assert (In d l1).
     rewrite Heql1. rewrite Heqf1.
     apply filter_In. split. auto.
     rewrite Ht5. auto. rewrite Heql1 in H5.
     rewrite Heqf1 in H5.
     pose proof (listmax_upperbound
                   (filter (fun y : A => if P y a0 =? 1 then true else false) l)
                   d f H5). omega.
     destruct H5. rewrite H5 in H4. simpl in H4.
     inversion H4. clear H4.
     assert (In d l2).
     rewrite Heql2. rewrite Heqg1.
     apply filter_In. split.  auto.
     rewrite H5. auto.
     assert (forall x, In x l1 -> forall y, In y l2 -> (f x < f y)%nat).
     intros. apply H1.
     apply Permutation_sym in H.
     pose proof (Hp A (l1 ++ l2) l y H). apply H10. firstorder.
     apply Permutation_sym in H.
     pose proof (Hp A (l1 ++ l2) l x H). apply H10. firstorder.
     assert (In x l). apply Permutation_sym in H.
     pose proof (Hp _ _ _ x H). apply H10. firstorder.
     assert (In y l). apply Permutation_sym in H.
     pose proof (Hp _ _ _ y H). apply H11. firstorder.
     pose proof (Ht1 y x H11 H10). destruct H12.
     destruct H13. destruct H14. destruct H15.
     destruct H16. destruct H17.
     pose proof (Ht2 x H7). pose proof (Ht3 y H9).
     destruct H19. destruct H20.
     pose proof (H18 H22 H21). auto.
     (* At this point, you grab the element x0 in list l1 which is equal to mx. 
        and give this as evidence in H7 *)
     rewrite <- Heqf1 in H8.
     rewrite <- Heql1 in H8.
     assert ((listmax f l1 < S (f d))%nat).
     clear H. clear H5. clear Heql1. clear Ht2. clear H8. 
     induction l1. simpl. omega.
     simpl. destruct l1. 
     pose proof (H7 a (in_eq a []) d H4). omega.
     apply Nat.max_lub_lt_iff. split.
     pose proof (H7 a (in_eq a (a1 :: l1)) d H4).
     omega. apply IHl1. firstorder.
     omega.

     (* In c l and d = a0 *)

     rewrite <- H3. rewrite <- H3 in H4.
     destruct (Adec c a0); destruct (Adec a0 a0);
       try auto; try congruence.
     assert ((if in_dec Adec c l then true else false) = true).
     destruct (in_dec Adec c l). auto. congruence.
     rewrite H5 in H4. clear H5. rewrite andb_true_r in H4.
     destruct (H2 c H0); try omega.
     destruct H5 as [Ht5 Ht6].
     rewrite Ht6 in H4. simpl in *.

     assert (In c l1).
     rewrite Heql1. rewrite Heqf1.
     apply filter_In. split. auto.
     rewrite Ht5. auto. rewrite Heql1 in H5.
     rewrite Heqf1 in H5.
     pose proof (listmax_upperbound
                   (filter (fun y : A => if P y a0 =? 1 then true else false) l)
                   c f H5). omega.
     destruct H5. rewrite H5 in H4. simpl in H4.
     inversion H4. clear H4.
     assert (In c l2).
     rewrite Heql2. rewrite Heqg1.
     apply filter_In. split.  auto.
     rewrite H5. auto.
     assert (forall x, In x l1 -> forall y, In y l2 -> (f x < f y)%nat).
     intros. apply H1.
     apply Permutation_sym in H.
     pose proof (Hp A (l1 ++ l2) l y H). apply H10. firstorder.
     apply Permutation_sym in H.
     pose proof (Hp A (l1 ++ l2) l x H). apply H10. firstorder.
     assert (In x l). apply Permutation_sym in H.
     pose proof (Hp _ _ _ x H). apply H10. firstorder.
     assert (In y l). apply Permutation_sym in H.
     pose proof (Hp _ _ _ y H). apply H11. firstorder.
     pose proof (Ht1 y x H11 H10). destruct H12.
     destruct H13. destruct H14. destruct H15.
     destruct H16. destruct H17.
     pose proof (Ht2 x H7). pose proof (Ht3 y H9).
     destruct H19. destruct H20.
     pose proof (H18 H22 H21). auto.
     (* At this point, you grab the element x0 in list l1 which is equal to mx. 
        and give this as evidence in H7 *)
     rewrite <- Heqf1 in H8.
     rewrite <- Heql1 in H8.
     assert ((listmax f l1 < S (f c))%nat).
     clear H. clear H5. clear Heql1. clear Ht2. clear H8. 
     induction l1. simpl. omega.
     simpl. destruct l1.
     pose proof (H7 a (in_eq a []) c H4). omega.
     apply Nat.max_lub_lt_iff. split.
     pose proof (H7 a (in_eq a (a1 :: l1)) c H4).
     omega. apply IHl1. firstorder.
     omega.

     (* In c l and In d l *)
     assert (Ht5: forall x, In x l1 -> forall y, In y l2 -> (f x < f y)%nat).
     intros. apply H1.
     apply Permutation_sym in H.
     pose proof (Hp A (l1 ++ l2) l y H). apply H7.
     firstorder.
     apply Permutation_sym in H.
     pose proof (Hp A (l1 ++ l2) l x H). apply H7.
     firstorder.
     apply Ht1.
     apply Permutation_sym in H.
     pose proof (Hp A (l1 ++ l2) l y H). apply H7.
     firstorder.
     apply Permutation_sym in H.
     pose proof (Hp A (l1 ++ l2) l x H). apply H7.
     firstorder. firstorder. firstorder.

     destruct (Adec c a0). 
     rewrite e in H0. pose proof (H2 a0 H0).
     firstorder.

     pose proof (H2 c H0). destruct H5 as [[Htt5 Htt6] | [Htt5 Htt6]].
     rewrite Htt6 in H4. simpl in H4.
     destruct (Adec d a0).  rewrite e in H3.
     firstorder.

     pose proof (H2 d H3). destruct H5 as [[Htt7 Htt8] | [Htt7 Htt8]].
     rewrite Htt8 in H4. simpl in H4.
     pose proof (H1 c d H0 H3). destruct H5. destruct H6. apply H6. auto.
     rewrite Htt7 in H4. simpl in H4.

     assert ((if in_dec Adec d l then true else false) = true).
     destruct (in_dec Adec d l). auto. congruence.
     rewrite H5 in H4. clear H5.
     assert (In c l1).
     rewrite Heql1. rewrite Heqf1.
     apply filter_In. split. auto.
     rewrite Htt5. auto.
     assert (In d l2).
     rewrite Heql2. rewrite Heqg1.
     apply filter_In. split. auto.
     rewrite Htt7. auto.
     pose proof (Ht5 c H5 d H6). omega.
     

     rewrite Htt5 in H4. simpl in H4.
     assert ((if in_dec Adec c l then true else false) = true).
     destruct (in_dec Adec c l). auto. congruence.
     rewrite H5 in H4. clear H5. destruct (Adec d a0).
     rewrite e in H3. firstorder.
     pose proof (H2 d H3). destruct H5 as [[Htt7 Htt8] | [Htt7 Htt8]].
     rewrite Htt8 in H4. simpl in H4.
     assert (In d l1).
     rewrite Heql1. rewrite Heqf1.
     apply filter_In. split. auto.
     rewrite Htt7. auto.
     assert (In c l2).
     rewrite Heql2. rewrite Heqg1.
     apply filter_In. split. auto.
     rewrite Htt5. auto.
     pose proof (Ht5 d H5 c H6). omega.

     rewrite Htt7 in H4. simpl in H4.
     assert ((if in_dec Adec d l then true else false) = true).
     destruct (in_dec Adec d l). auto. congruence.
     rewrite H5 in H4. clear H5. 
     pose proof (H1 c d H0 H3). destruct H5. destruct H6.
     apply H6. omega.

     (* Finish P c d = 0 case *)

     pose proof Permutation_in as Hp.
     (* Starting P c d = -1 *) 
     split; intros.
      assert (forall (n m : nat), (n < m)%nat -> (m > n)%nat)
       by auto with arith. apply H5. clear H5.
     destruct H0; destruct H3;
       try congruence; try auto; try omega.
     
     (* c = a0, In d l *)
     rewrite <- H0. rewrite <- H0 in H4.
     destruct (Adec a0 a0).
     destruct (Adec d a0). congruence.
     rewrite H4.  simpl.

     pose proof Permutation_in. 
     pose proof (H5 A l (l1 ++ l2) d H H3).
     apply in_app_iff in H6. destruct H6.
     pose proof (Ht2 d H6).
     rewrite <- Heqf1.
     rewrite <- Heql1.  
     pose proof (listmax_upperbound l1 d f H6). omega. 
     pose proof (Ht3 d H6). omega. congruence.

     (* In c l, d = a0 *)
     rewrite <- H3. rewrite <- H3 in H4.
     destruct (Adec a0 a0).
     destruct (Adec c a0). congruence.
     pose proof (H2 c H0); try congruence.
     destruct H5. destruct H5.
     try congruence. destruct H5. 
     rewrite H5.  simpl.
     assert ((if in_dec Adec c l then true else false) = true).
     destruct (in_dec Adec c l). auto. congruence.
     rewrite H7. clear H7. apply lt_n_S.
     rewrite <- Heqf1. rewrite <- Heql1.
 
     assert (In c l2).
     rewrite Heql2. rewrite Heqg1.
     apply filter_In. split.  auto.
     rewrite H5. auto.

     assert (forall x, In x l1 -> forall y, In y l2 -> (f x < f y)%nat).
     intros. apply H1.
     apply Permutation_sym in H.
     pose proof (Hp A (l1 ++ l2) l y H). apply H10. firstorder.
     apply Permutation_sym in H.
     pose proof (Hp A (l1 ++ l2) l x H). apply H10. firstorder.
     assert (In x l). apply Permutation_sym in H.
     pose proof (Hp _ _ _ x H). apply H10. firstorder.
     assert (In y l). apply Permutation_sym in H.
     pose proof (Hp _ _ _ y H). apply H11. firstorder.
     pose proof (Ht1 y x H11 H10). destruct H12.
     destruct H13. destruct H14. destruct H15.
     destruct H16. destruct H17.
     pose proof (Ht2 x H8). pose proof (Ht3 y H9).
     destruct H19. destruct H20.
     pose proof (H18 H22 H21). auto.

     (* At this point, you grab the element x0 in list l1 which is equal to mx. 
        and give this as evidence in H7 *) 
     assert ((listmax f l1 < S (f c))%nat).
     clear H. clear H5. clear Heql1. clear Ht2.
     induction l1. simpl. omega.
     simpl. destruct l1.
     pose proof (H8 a (in_eq a []) c H7). omega.
     apply Nat.max_lub_lt_iff. split.
     pose proof (H8 a (in_eq a (a1 :: l1)) c H7).
     omega. apply IHl1. firstorder.
     omega. congruence.


     (* P c d = -1 *)

     pose proof (H1 c d H0 H3). 
     destruct (Adec d a0); destruct (Adec c a0);
       try congruence.
     rewrite e in H3.
     pose proof (H2 c H0).
     destruct H6. destruct H6.
     rewrite H7. simpl.
     rewrite <- Heqf1. rewrite <- Heql1.
     rewrite e in H4. congruence.
     destruct H6. rewrite H6. rewrite e in H4.
     simpl.
     assert ((if in_dec Adec c l then true else false) = true).
     destruct (in_dec Adec c l). auto. congruence. 
     rewrite H8. clear H8.  apply lt_n_S.
     rewrite <- Heqf1. rewrite <- Heql1.
     assert (In c l2).
     rewrite Heql2. rewrite Heqg1.
     apply filter_In. split.  auto.
     rewrite H6. auto.
 
     assert (forall x, In x l1 -> forall y, In y l2 -> (f x < f y)%nat).
     intros. apply H1.
     apply Permutation_sym in H.
     pose proof (Hp A (l1 ++ l2) l y H). apply H11. firstorder.
     apply Permutation_sym in H.
     pose proof (Hp A (l1 ++ l2) l x H). apply H11. firstorder.
     assert (In x l). apply Permutation_sym in H.
     pose proof (Hp _ _ _ x H). apply H11. firstorder.
     assert (In y l). apply Permutation_sym in H.
     pose proof (Hp _ _ _ y H). apply H12. firstorder.
     pose proof (Ht1 y x H12 H11). destruct H13.
     destruct H14. destruct H15. destruct H16.
     destruct H17. destruct H18.
     pose proof (Ht2 x H9). pose proof (Ht3 y H10).
     destruct H20. destruct H21.
     pose proof (H19 H23 H22). auto.
     (* At this point, you grab the element x0 in list l1 which is equal to mx. 
        and give this as evidence in H7 *)
     assert ((listmax f l1 < S (f c))%nat).
     clear H. clear H5. clear Heql1. clear Ht2. 
     induction l1. simpl. omega.
     simpl. destruct l1.
     pose proof (H9 a (in_eq a []) c H8). omega.
     apply Nat.max_lub_lt_iff. split.
     pose proof (H9 a (in_eq a (a1 :: l1)) c H8).
     omega. apply IHl1. firstorder.
     omega.

     (* d <> a0 and c = a0. Play the same trick *)

     pose proof (H2 d H3).
     destruct H6. destruct H6.
     rewrite H7. simpl.
     rewrite <- Heqf1. rewrite <- Heql1.
     rewrite e in H4. 
     assert (In d l1).
     rewrite Heql1. rewrite Heqf1.
     apply filter_In. split.  auto.
     rewrite H6. auto.
 
     assert (forall x, In x l1 -> forall y, In y l2 -> (f x < f y)%nat).
     intros. apply H1.
     apply Permutation_sym in H.
     pose proof (Hp A (l1 ++ l2) l y H). apply H11. firstorder.
     apply Permutation_sym in H.
     pose proof (Hp A (l1 ++ l2) l x H). apply H11. firstorder.
     assert (In x l). apply Permutation_sym in H.
     pose proof (Hp _ _ _ x H). apply H11. firstorder.
     assert (In y l). apply Permutation_sym in H.
     pose proof (Hp _ _ _ y H). apply H12. firstorder.
     pose proof (Ht1 y x H12 H11). destruct H13.
     destruct H14. destruct H15. destruct H16.
     destruct H17. destruct H18.
     pose proof (Ht2 x H9). pose proof (Ht3 y H10).
     destruct H20. destruct H21.
     pose proof (H19 H23 H22). auto.
     pose proof (listmax_upperbound l1 d f H8). omega.
     destruct H6. congruence.

     (* In c l and In d l *)
     assert (Ht5: forall x, In x l1 -> forall y, In y l2 -> (f x < f y)%nat).
     intros. apply H1.
     apply Permutation_sym in H.
     pose proof (Hp A (l1 ++ l2) l y H). apply H8.
     firstorder.
     apply Permutation_sym in H.
     pose proof (Hp A (l1 ++ l2) l x H). apply H8.
     firstorder.
     apply Ht1.
     apply Permutation_sym in H.
     pose proof (Hp A (l1 ++ l2) l y H). apply H8.
     firstorder.
     apply Permutation_sym in H.
     pose proof (Hp A (l1 ++ l2) l x H). apply H8.
     firstorder. firstorder. firstorder.

  

     pose proof (H2 c H0). destruct H6 as [[Htt5 Htt6] | [Htt5 Htt6]].
     rewrite Htt6. simpl. 

     pose proof (H2 d H3). destruct H6 as [[Htt7 Htt8] | [Htt7 Htt8]].
     rewrite Htt8. simpl.
     pose proof (H1 c d H0 H3). destruct H6. destruct H7.
     pose proof ((proj1 H8) H4). omega.

     assert ((if in_dec Adec d l then true else false) = true).
     destruct (in_dec Adec d l). auto. congruence.
     rewrite H6. clear H6.
     assert (In c l1).
     rewrite Heql1. rewrite Heqf1.
     apply filter_In. split. auto.
     rewrite Htt5. auto.
     assert (In d l2).
     rewrite Heql2. rewrite Heqg1.
     apply filter_In. split. auto.
     rewrite Htt7. auto. rewrite Htt7. simpl.
     pose proof (Ht5 c H6 d H7). omega.
     

     rewrite Htt5. simpl. 
     assert ((if in_dec Adec c l then true else false) = true).
     destruct (in_dec Adec c l). auto. congruence.
     rewrite H6. clear H6.
     pose proof (H2 d H3). destruct H6 as [[Htt7 Htt8] | [Htt7 Htt8]].
     rewrite Htt8. simpl. 
     assert (In d l1).
     rewrite Heql1. rewrite Heqf1.
     apply filter_In. split. auto.
     rewrite Htt7. auto.
     assert (In c l2).
     rewrite Heql2. rewrite Heqg1.
     apply filter_In. split. auto.
     rewrite Htt5. auto.
     pose proof (Ht5 d H6 c H7). omega.

     rewrite Htt7. simpl. 
     assert ((if in_dec Adec d l then true else false) = true).
     destruct (in_dec Adec d l). auto. congruence.
     rewrite H6. clear H6. 
     pose proof (H1 c d H0 H3). destruct H6. destruct H7.
     pose proof ((proj1 H8) H4). omega.



     destruct H0; destruct H3; try auto;
       try congruence.
     rewrite <- H0 in H4. rewrite <- H3 in H4.
     firstorder.
      
     (* c = a0, In d l *)
     rewrite <- H0. rewrite <- H0 in H4.
     destruct (Adec a0 a0); destruct (Adec d a0);
       try auto; try congruence. firstorder.
     assert ((if in_dec Adec d l then true else false) = true).
     destruct (in_dec Adec d l). auto. congruence.
     rewrite H5 in H4. clear H5. rewrite andb_true_r in H4.
     destruct (H2 d H3); try omega.
     destruct H5 as [Ht5 Ht6].
     rewrite Ht5 in H4. simpl in *.

     assert (In d l2).
     rewrite Heql2. rewrite Heqg1.
     apply filter_In. split. auto.
     rewrite Ht5. auto.  rewrite <- Heqf1 in H4.
     rewrite <- Heql1 in H4.

     assert (forall x, In x l1 -> forall y, In y l2 -> (f x < f y)%nat).
     intros. apply H1.
     apply Permutation_sym in H.
     pose proof (Hp A (l1 ++ l2) l y H). apply H8. firstorder.
     apply Permutation_sym in H.
     pose proof (Hp A (l1 ++ l2) l x H). apply H8. firstorder.
     assert (In x l). apply Permutation_sym in H.
     pose proof (Hp _ _ _ x H). apply H8. firstorder.
     assert (In y l). apply Permutation_sym in H.
     pose proof (Hp _ _ _ y H). apply H9. firstorder.
     pose proof (Ht1 y x H9 H8). destruct H10.
     destruct H11. destruct H12. destruct H13.
     destruct H14. destruct H15.
     pose proof (Ht2 x H6). pose proof (Ht3 y H7).
     destruct H17. destruct H18.
     pose proof (H16 H20 H19). auto.
 
     assert ((listmax f l1 < S (f d))%nat).
     clear H.  clear H4. clear Heql1. clear Ht2.  
     induction l1. simpl. omega.
     simpl. destruct l1. 
     pose proof (H6 a (in_eq a []) d H5). omega.
     apply Nat.max_lub_lt_iff. split.
     pose proof (H6 a (in_eq a (a1 :: l1)) d H5).
     omega. apply IHl1. firstorder.
     omega.

     (* In c l, d = a0. Play the same trick *)
     
     rewrite <- H3. rewrite <- H3 in H4.
     destruct (Adec a0 a0); destruct (Adec c a0);
       try auto; try congruence. firstorder.
     assert ((if in_dec Adec c l then true else false) = true).
     destruct (in_dec Adec c l). auto. congruence.
     rewrite H5 in H4. clear H5. rewrite andb_true_r in H4.
     destruct (H2 c H0); try omega.
     destruct H5 as [Ht5 Ht6].
     rewrite Ht6 in H4. simpl in *.
     
     assert (In c l1).
     rewrite Heql1. rewrite Heqf1.
     apply filter_In. split. auto.
     rewrite Ht5. auto.  rewrite <- Heqf1 in H4.
     rewrite <- Heql1 in H4.
     pose proof (listmax_upperbound l1 c f H5). omega.

     (* In c l, and In d l *)
     assert (Ht5: forall x, In x l1 -> forall y, In y l2 -> (f x < f y)%nat).
     intros. apply H1.
     apply Permutation_sym in H.
     pose proof (Hp A (l1 ++ l2) l y H). apply H7.
     firstorder.
     apply Permutation_sym in H.
     pose proof (Hp A (l1 ++ l2) l x H). apply H7.
     firstorder.
     apply Ht1.
     apply Permutation_sym in H.
     pose proof (Hp A (l1 ++ l2) l y H). apply H7.
     firstorder.
     apply Permutation_sym in H.
     pose proof (Hp A (l1 ++ l2) l x H). apply H7.
     firstorder. firstorder. firstorder.

     destruct (Adec c a0). 
     rewrite e in H0. pose proof (H2 a0 H0).
     firstorder.

     pose proof (H2 c H0). destruct H5 as [[Htt5 Htt6] | [Htt5 Htt6]].
     rewrite Htt6 in H4. simpl in H4.
     destruct (Adec d a0).  rewrite e in H3.
     firstorder.

     pose proof (H2 d H3). destruct H5 as [[Htt7 Htt8] | [Htt7 Htt8]].
     rewrite Htt8 in H4. simpl in H4.
     pose proof (H1 c d H0 H3). destruct H5. destruct H6. apply H7. auto.
     rewrite Htt7 in H4. simpl in H4.

     assert ((if in_dec Adec d l then true else false) = true).
     destruct (in_dec Adec d l). auto. congruence.
     rewrite H5 in H4. clear H5.
     assert (In c l1).
     rewrite Heql1. rewrite Heqf1.
     apply filter_In. split. auto.
     rewrite Htt5. auto.
     assert (In d l2).
     rewrite Heql2. rewrite Heqg1.
     apply filter_In. split. auto.
     rewrite Htt7. auto.
     pose proof (Ht5 c H5 d H6). omega.

     rewrite Htt5 in H4. simpl in H4.
     assert ((if in_dec Adec c l then true else false) = true).
     destruct (in_dec Adec c l). auto. congruence.
     rewrite H5 in H4. clear H5. destruct (Adec d a0).
     rewrite e in H3. firstorder.
     pose proof (H2 d H3). destruct H5 as [[Htt7 Htt8] | [Htt7 Htt8]].
     rewrite Htt8 in H4. simpl in H4.
     assert (In d l1).
     rewrite Heql1. rewrite Heqf1.
     apply filter_In. split. auto.
     rewrite Htt7. auto.
     assert (In c l2).
     rewrite Heql2. rewrite Heqg1.
     apply filter_In. split. auto.
     rewrite Htt5. auto.
     pose proof (Ht5 d H5 c H6).
     pose proof (H1 c d H0 H3).
     destruct H8. destruct H9. apply H10. omega.

     rewrite Htt7 in H4. simpl in H4.
     assert ((if in_dec Adec d l then true else false) = true).
     destruct (in_dec Adec d l). auto. congruence.
     rewrite H5 in H4. clear H5. 
     pose proof (H1 c d H0 H3). destruct H5. destruct H6.
     apply H7. omega.
   Qed.



   (* Two different ranked candidates *)
   Definition phi_one a l :=
     (forall (x : A), In x l -> (P x a = 1 /\ P a x = -1)
                          \/ (P x a = -1 /\ P a x = 1)).

   (* Same ranked *)
   Definition phi_two a l0 l1 :=
     exists (a0' : A), In a0' l0 /\
                  (forall (x : A), In x l1 ->
                              (P a x = P a0' x) /\
                              (P x a = P x a0')).

          
   Lemma phi_one_helper :
     forall x a,
       {((P x a = 1 /\ P a x = -1) \/ (P x a = -1 /\ P a x = 1))} +
       {~((P x a = 1 /\ P a x = -1) \/ (P x a = -1 /\ P a x = 1))}.
   Proof.
     intros x a.
     destruct (Pdec x a) as [[H | H] | H];
       destruct (Pdec a x) as [[H1 | H1] | H1];
       try auto; try right; try firstorder.
   Qed.

   Lemma phi_two_helper : forall (a x a0' : A),
       {((P a x = P a0' x) /\ (P x a = P x a0'))} +
       {~((P a x = P a0' x) /\ (P x a = P x a0'))}.
   Proof.
     intros a x a0'.
     destruct (Pdec a x) as [[H | H] | H],
                            (Pdec a0' x) as [[H1 | H1] | H1],
                                            (Pdec x a) as [[H2 | H2] | H2],
                                                          (Pdec x a0') as [[H3 | H3] | H3];
       firstorder.
   Qed.


   Lemma phi_two_inhanced : forall a l a0',
       {(forall x : A, In x l -> (P a x = P a0' x) /\
                          (P x a = P x a0'))} +
       {~(forall x : A, In x l -> (P a x = P a0' x) /\
                            (P x a = P x a0'))}.
   Proof.
     intros a l a0'.
     induction l.
     + left; intros; intuition.
     + destruct IHl.
       destruct (phi_two_helper a a0 a0').
       left. intros. destruct H. subst. assumption.
       apply a1; auto.
       right. unfold not; intros.
       apply n. apply H. intuition.
       right. unfold not in *; intros.
       apply n. intros. apply H.
       intuition.
   Qed.

   Lemma phi_one_dec :
     forall a l, {phi_one a l} + {~(phi_one a l)}.
   Proof.
     intros a l.
     induction l.
     left. unfold phi_one. intros. inversion H.
     destruct IHl.
     unfold phi_one in *.
     destruct (phi_one_helper a0 a).
     left. intros. destruct H. subst. assumption.
     apply p. assumption.
     right. unfold not. intros.
     apply n. apply H. simpl. left. auto.
     right. unfold not in *. intros.
     apply n. unfold phi_one in *.
     intros. apply H. simpl. right. auto.
   Qed.


   Lemma phi_two_dec : forall a l1 l2,
       {phi_two a l1 l2} + {~phi_two a l1 l2}.
   Proof.
     intros a l1 l2.
     induction l1.
     right. unfold not. intros. unfold phi_two in *.
     destruct H. destruct H. inversion H.
     
     destruct IHl1.  unfold phi_two in *.
     destruct (phi_two_inhanced a l2 a0).
     left.   exists a0.
     split. simpl. left. auto.
     assumption. 
     left. destruct p. exists x.
     destruct H. split. simpl. right. auto.
     assumption.
     
     destruct (phi_two_inhanced a l2 a0).
     left. exists a0. split. simpl. auto.
     assumption.
     right. unfold not in *. intros.
     unfold phi_two in H. destruct H. destruct H.
     destruct H. subst. apply n0. assumption.
     apply n. unfold phi_two. exists x. split.
     auto. assumption.
   Qed.

    Definition phi a l := phi_two a l l \/ phi_one a l.
 
                       
    Lemma phi_decidable :
      forall a l, {phi a l} + {~(phi a l)}. 
    Proof.
      intros a l.
      unfold phi.
      destruct (phi_two_dec a l l), (phi_one_dec a l); intuition.
    Qed.

    Lemma not_in_list : forall (a : A) (l : list A) (f : A -> nat),
        ~In (f a) (map f l) -> (forall x, In x l -> f a <> f x).  
    Proof.
      intros a l f Hnin x Hx.
      pose proof (in_map f l x Hx).
      pose proof (not_equal_elem _ (f x) (f a) (map f l)  H Hnin).
      auto.
    Qed.

    Theorem transitive_dec_first_fn :
      forall c d e,
        {((P c d = 1 -> P d e = 1 -> P c e = 1) /\
          (P c d = 1 -> P d e = 0 -> P c e = 1) /\
          (P c d = 0 -> P d e = 1 -> P c e = 1) /\
          (P c d = 0 -> P d e = 0 -> P c e = 0) /\
          (P c d = 0 -> P d e = -1 -> P c e = -1) /\
          (P c d = -1 -> P d e = 0 -> P c e = -1) /\
          (P c d = -1 -> P d e = -1 -> P c e = -1))} +
        {~((P c d = 1 -> P d e = 1 -> P c e = 1) /\
          (P c d = 1 -> P d e = 0 -> P c e = 1) /\
          (P c d = 0 -> P d e = 1 -> P c e = 1) /\
          (P c d = 0 -> P d e = 0 -> P c e = 0) /\
          (P c d = 0 -> P d e = -1 -> P c e = -1) /\
          (P c d = -1 -> P d e = 0 -> P c e = -1) /\
          (P c d = -1 -> P d e = -1 -> P c e = -1))}.   
    Proof.
      intros.
       destruct (Pdec c d) as [[H | H] | H],
                            (Pdec d e) as [[H1 | H1] | H1],
                                          (Pdec c e) as [[H2 | H2] | H2];
         firstorder.
    Qed.

    Theorem transitive_dec_second_fn :
      forall c d l,
        {(forall e, In e l ->
               ((P c d = 1 -> P d e = 1 -> P c e = 1) /\
                (P c d = 1 -> P d e = 0 -> P c e = 1) /\
                (P c d = 0 -> P d e = 1 -> P c e = 1) /\
                (P c d = 0 -> P d e = 0 -> P c e = 0) /\
                (P c d = 0 -> P d e = -1 -> P c e = -1) /\
                (P c d = -1 -> P d e = 0 -> P c e = -1) /\
                (P c d = -1 -> P d e = -1 -> P c e = -1)))} +
        {~(forall e, In e l ->
                ((P c d = 1 -> P d e = 1 -> P c e = 1) /\
                 (P c d = 1 -> P d e = 0 -> P c e = 1) /\
                 (P c d = 0 -> P d e = 1 -> P c e = 1) /\
                 (P c d = 0 -> P d e = 0 -> P c e = 0) /\
                 (P c d = 0 -> P d e = -1 -> P c e = -1) /\
                 (P c d = -1 -> P d e = 0 -> P c e = -1) /\
                 (P c d = -1 -> P d e = -1 -> P c e = -1)))}.
    Proof.
      intros. induction l.
      left; intuition.
      destruct IHl. 
      destruct (transitive_dec_first_fn c d a) as [H | H]. 
      left. intros.  destruct H0; subst; firstorder.
      right. unfold not. intros. apply H.
      pose proof (H0 a (in_eq a l)). firstorder.

      destruct (transitive_dec_first_fn c d a) as [H | H].
      right. unfold not. intros. apply n. intuition.
      right. intuition.
    Qed.

    Theorem transitive_dec_third_fn :
      forall c l1 l2,
        {(forall d e, In d l1 -> In e l2 -> 
                 ((P c d = 1 -> P d e = 1 -> P c e = 1) /\
                  (P c d = 1 -> P d e = 0 -> P c e = 1) /\
                  (P c d = 0 -> P d e = 1 -> P c e = 1) /\
                  (P c d = 0 -> P d e = 0 -> P c e = 0) /\
                  (P c d = 0 -> P d e = -1 -> P c e = -1) /\
                  (P c d = -1 -> P d e = 0 -> P c e = -1) /\
                  (P c d = -1 -> P d e = -1 -> P c e = -1)))} +
        {~(forall d e, In d l1 -> In e l2 -> 
                  ((P c d = 1 -> P d e = 1 -> P c e = 1) /\
                   (P c d = 1 -> P d e = 0 -> P c e = 1) /\
                   (P c d = 0 -> P d e = 1 -> P c e = 1) /\
                   (P c d = 0 -> P d e = 0 -> P c e = 0) /\
                   (P c d = 0 -> P d e = -1 -> P c e = -1) /\
                   (P c d = -1 -> P d e = 0 -> P c e = -1) /\
                   (P c d = -1 -> P d e = -1 -> P c e = -1)))}.
    Proof.
      intros.
      induction l1.
      left; intuition.
      destruct IHl1.
      pose proof (transitive_dec_second_fn c a l2).
      destruct H.
      left. intros. destruct H. subst. firstorder.
      specialize (a0  d e H H0). firstorder.
      right. unfold not. intros. apply n. intros. firstorder.
      right. unfold not; intros. firstorder.
    Qed.

    Theorem transitive_dec_fourth_fn :
      forall l1 l2 l3,
        {(forall c d e, In c l1 -> In d l2 -> In e l3 ->
                   ((P c d = 1 -> P d e = 1 -> P c e = 1) /\
                    (P c d = 1 -> P d e = 0 -> P c e = 1) /\
                    (P c d = 0 -> P d e = 1 -> P c e = 1) /\
                    (P c d = 0 -> P d e = 0 -> P c e = 0) /\
                    (P c d = 0 -> P d e = -1 -> P c e = -1) /\
                    (P c d = -1 -> P d e = 0 -> P c e = -1) /\
                    (P c d = -1 -> P d e = -1 -> P c e = -1)))} +
        {~(forall c d e, In c l1 -> In d l2 -> In e l3 ->
                   ((P c d = 1 -> P d e = 1 -> P c e = 1) /\
                    (P c d = 1 -> P d e = 0 -> P c e = 1) /\
                    (P c d = 0 -> P d e = 1 -> P c e = 1) /\
                    (P c d = 0 -> P d e = 0 -> P c e = 0) /\
                    (P c d = 0 -> P d e = -1 -> P c e = -1) /\
                    (P c d = -1 -> P d e = 0 -> P c e = -1) /\
                    (P c d = -1 -> P d e = -1 -> P c e = -1)))}.
    Proof.
      intros.
      induction l1.
      left; intuition.
      destruct IHl1.
      pose proof (transitive_dec_third_fn a l2 l3).
      destruct H.
      left. intros. destruct H. subst. firstorder.
      specialize (a0 c d e H H0 H1). firstorder.
      right. firstorder.
      right. firstorder.
    Qed.

    Theorem transitive_dec_fn :
      forall l,
        {(forall c d e, In c l -> In d l -> In e l ->
                   ((P c d = 1 -> P d e = 1 -> P c e = 1) /\
                    (P c d = 1 -> P d e = 0 -> P c e = 1) /\
                    (P c d = 0 -> P d e = 1 -> P c e = 1) /\
                    (P c d = 0 -> P d e = 0 -> P c e = 0) /\
                    (P c d = 0 -> P d e = -1 -> P c e = -1) /\
                    (P c d = -1 -> P d e = 0 -> P c e = -1) /\
                    (P c d = -1 -> P d e = -1 -> P c e = -1)))} +
        {~(forall c d e, In c l -> In d l -> In e l ->
                   ((P c d = 1 -> P d e = 1 -> P c e = 1) /\
                    (P c d = 1 -> P d e = 0 -> P c e = 1) /\
                    (P c d = 0 -> P d e = 1 -> P c e = 1) /\
                    (P c d = 0 -> P d e = 0 -> P c e = 0) /\
                    (P c d = 0 -> P d e = -1 -> P c e = -1) /\
                    (P c d = -1 -> P d e = 0 -> P c e = -1) /\
                    (P c d = -1 -> P d e = -1 -> P c e = -1)))}.
    Proof.
      intros.
      pose proof (transitive_dec_fourth_fn l l l). auto.
    Qed.
    
    
      
      

    Lemma vl_or_notvl : forall l : list A, vl l + ~vl l.
    Proof. 
      induction l.
      left; exists (fun _ => 0)%nat; intros; intuition.
      destruct IHl. 
      pose proof (validity_after_remove_cand l a).
      pose proof (Pdec a a) as [[H1 | H1] | H1].
      right. firstorder.
      pose proof (transitive_dec_fn (a :: l)).
      destruct H0.
      pose proof (phi_decidable a l).
      destruct H0.
      left. apply H. split. auto. split. auto.
      split. auto. split. intros.
      pose proof (a0 c a e (or_intror H0) (in_eq a l) (or_intror H2)). auto.
      unfold phi in p. unfold phi_two, phi_one in p.
      destruct p. left. auto.
      right. intros. specialize (H0 x H2). destruct H0.
      left. auto. right. destruct H0. split. auto. auto.

      right. unfold not. intros. apply n. unfold vl in H0.
      destruct H0 as [f Hf]. unfold phi. unfold phi_two, phi_one.

      assert (Hnat : forall x y : nat, {x = y} + {x <> y}) by (auto with arith).
      
      pose proof (in_dec Hnat (f a) (map f l)).  clear Hnat.
      destruct H0.
      apply in_map_iff in i. destruct i as [x [Hl Hr]].

      
      left. exists x. split. auto.
      intros. split.   
      pose proof (Hf a x0 (in_eq a l) (or_intror H0)).
      pose proof (Hf x x0 (or_intror Hr) (or_intror H0)).
      destruct H2. destruct H4.
      destruct H3. destruct H6.
      destruct (Pdec a x0) as [[H8 | H8] | H8];
        destruct (Pdec x x0) as [[H9 | H9] | H9].
      rewrite H8, H9. auto.
      apply H5 in H8. apply H6 in H9.
      rewrite <- Hl in H8.
      rewrite H9 in H8. 
      apply gt_irrefl in H8. inversion H8.
      apply H5 in H8. apply H3 in H9.
      rewrite <- Hl in H8. 
      apply gt_asym in H8. 
      assert (f x0 > f x)%nat by omega.
      unfold not in H8. apply H8 in H10. inversion H10.
      apply H4 in H8. apply H7 in H9. rewrite <- Hl in H8. omega.
      rewrite H8, H9. auto.
      rewrite H4 in H8. rewrite H3 in H9.
      rewrite Hl in H9. omega.
      rewrite H2 in H8. rewrite H7 in H9.
      rewrite Hl in H9. omega.
      rewrite H2 in H8. rewrite H6 in H9.
      rewrite Hl in H9. omega.
      rewrite H8, H9. auto.

      pose proof (Hf x0 a (or_intror H0) (in_eq a l)).
      pose proof (Hf x0 x (or_intror H0) (or_intror Hr)).
      destruct H2. destruct H4.
      destruct H3. destruct H6.
      destruct (Pdec x0 a) as [[H8 | H8] | H8];
        destruct (Pdec x0 x) as [[H9 | H9] | H9].
      rewrite H8, H9. auto.
      apply H5 in H8. apply H6 in H9.
      rewrite <- Hl in H8.
      rewrite H9 in H8. 
      apply gt_irrefl in H8. inversion H8.
      apply H5 in H8. apply H3 in H9.
      rewrite <- Hl in H8. 
      apply gt_asym in H8.  
      assert (f x > f x0)%nat by omega.
      unfold not in H8. apply H8 in H10. inversion H10.
      apply H4 in H8. apply H7 in H9. rewrite <- Hl in H8.
      rewrite H8 in H9. apply gt_irrefl in H9. inversion H9.
      rewrite H8, H9. auto.
      rewrite H4 in H8. rewrite H3 in H9.
      rewrite Hl in H9. rewrite H8 in H9.
      apply lt_irrefl in H9. inversion H9. 
      rewrite H2 in H8. rewrite H7 in H9.
      rewrite Hl in H9.  apply gt_asym in H9.
      (* it might shut here *)
      assert (f a > f x0)%nat by omega.
      apply H9 in H10. inversion H10.
      rewrite H2 in H8. rewrite H6 in H9.
      rewrite Hl in H9. rewrite H9 in H8.
      apply lt_irrefl in H8. inversion H8.
      rewrite H8, H9. auto.
 
      right. intros x Hx.
      destruct (lt_eq_lt_dec (f a) (f x)) as [[H2 | H2] | H2].
      pose proof (Hf a x (in_eq a l) (or_intror Hx)).
      destruct H0.
      right.
      pose proof (Hf x a (or_intror Hx) (in_eq a l)).
      destruct H4. destruct H5.
      split.  apply H6. firstorder.
      apply H0. firstorder.
      pose proof (not_in_list a l f n0 x Hx). firstorder.      

      left. pose proof (Hf x a (or_intror Hx) (in_eq a l)).
      destruct H0. destruct H3. split. apply H0. assumption.
      pose proof (Hf a x (in_eq a l) (or_intror Hx)). destruct H5.
      destruct H6. apply H7. firstorder.


      right. unfold vl. unfold not. intros. apply n. 
      intros. destruct H0 as [f Hv].  clear n.
      destruct (Hv c d H2 H3) as [H6 [H7 H8]].
      destruct (Hv d e H3 H4) as [H9 [H10 H11]].
      destruct (Hv c e H2 H4) as [H12 [H13 H14]].
      split. intros. apply H6 in H0. apply H9 in H5.
      apply H12. eapply Nat.lt_trans with (f d).
      assumption. assumption.
      split. intros. apply H6 in H0. apply H10 in H5.
      apply H12. rewrite H5 in H0. assumption.
      split. intros. apply H7 in H0. apply H9 in H5.
      apply H12. rewrite <- H0 in H5. assumption.
      split. intros. apply H7 in H0. apply H10 in H5.
      apply H13. rewrite <- H0 in H5.  assumption.
      split. intros. apply H7 in H0. apply H11 in H5.
      apply H14. rewrite <- H0 in H5. assumption.
      split. intros. apply H8 in H0. apply H10 in H5. 
      apply H14.  rewrite H5 in H0. assumption.
      intros. apply H8 in H0. apply H11 in H5.
      apply H14. eapply gt_trans with (f d).
      assumption. assumption.
      (* P a a = 1 which is invalid *)
      right.  unfold not.  intros.
      apply H in H0.  destruct H0 as [Hv [Hp Hrest]].
      rewrite H1 in Hp. inversion Hp.
      right. firstorder.
    Qed.
          

    Definition valid := exists (f : A -> nat), forall (c d : A),
          ((P c d = 1 <-> (f c < f d)%nat) /\
           (P c d = 0 <-> (f c = f d)%nat) /\
           (P c d = -1 <-> (f c > f d)%nat)).

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

    Definition perm (sig : A -> A) (c d : A) := P (sig c) (sig d).

End Cand.
 
Require Import Coq.Logic.FinFun. 
