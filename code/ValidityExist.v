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
     split; split; intros. 
     rewrite <- H in H4. rewrite <- H0 in H4.
     omega.
     rewrite <- H0 in H4. rewrite <- H in H4.
     firstorder.

     split; intros. subst. firstorder.
     subst. auto.

     split; intros. subst. omega.
     subst. firstorder.

     split.
     split; intros.
     rewrite  <- H. rewrite <- H in H4.
     
     
     