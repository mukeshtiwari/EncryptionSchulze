Require Import Notations.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Le.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.omega.Omega.
Require Import Bool.Sumbool.
Require Import Bool.Bool.
Require Import Coq.Logic.ConstructiveEpsilon.
Require Import Coq.ZArith.ZArith.
Require Import ListLemma.
Import ListNotations.



Notation "'existsT' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'existsT' '/ ' x .. y , '/ ' p ']'") : type_scope.


Section Cand.    

  Variable A : Type.
  Variable P : A -> A -> Prop.
  Hypothesis Adec : forall (c d : A), {c = d} + {c <> d}. (* A is decidable *)
  Hypothesis Pdec : forall c d, P c d \/ ~P c d. (* P is decidable *)
  
  (* A is finite. finite : Type -> Type *)
  Definition finite := existsT (l : list A), forall (a : A), In a l.

  (* vl : forall A : Type, (P : A -> A -> Prop) -> (list A) -> Prop *)
  Definition vl (l : list A) :=
    exists (f : A -> nat), forall (c d : A), In c l -> In d l -> (P c d <-> (f c < f d)%nat).

  
  Lemma validity_after_remove_cand :
    forall (l : list A) (a0 : A),
      vl (a0 :: l) <->
      vl l /\
      ((exists (a0' : A), In a0' l /\ forall (x : A), In x l -> (P a0 x <-> P a0' x) /\
                                                    (P x a0 <-> P x a0')) \/
       (forall (x : A), In x l -> P a0 x \/ P x a0)).
  Proof.
    unfold vl; split; intros.
    destruct H as [f H]. 
    split.
    exists f. firstorder.

    assert (Hnat : forall x y : nat, {x = y} + {x <> y}) by (auto with arith).
      
    pose proof (in_dec Hnat (f a0) (map f l)). clear Hnat.
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
    firstorder.

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
    
    destruct H as [[f H1] [[a [H2 H3]] | H2]].    
    (* From H3, I know that f a = f a0  so I am going to supply same function *)
    exists f. intros c d H4 H5. destruct H4, H5.
    split; intros.
    rewrite <- H in H4. rewrite <- H0 in H4.
    (* There is no way to construct f a0 < f a0 from P a0 a0 or I am missing something *)
    
    
   
    
  Lemma vl_or_notvl : forall l : list A, vl l + ~vl l.
  Proof.
    intros l.
    pose proof (validity_after_remove_cand l).
    induction l. left. unfold not; intros.
    unfold vl in *. exists (fun _ => 0%nat). intros. inversion H0.
    pose proof (H a). destruct H0.
    
  Definition valid := exists (f : A -> nat), forall (c d : A), P c d <-> (f c < f d)%nat.

  Lemma from_vl_to_valid : forall l : list A, (forall a : A, In a l -> valid <-> vl l).
  Proof.
  Admitted.
  
  Lemma decidable_valid : finite -> {valid} + {~valid}.
  Proof.
    unfold finite, valid.
    intros H. destruct H as [l Hin].
    pose proof (from_vl_to_valid l Hin).
    destruct H.  fi
    
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
    
