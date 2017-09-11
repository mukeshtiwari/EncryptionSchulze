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
    exists (f : A -> nat), forall (c d : A) (Hc : In c l) (Hd : In d l), (P c d <-> (f c < f d)%nat).

  
  Lemma validity_after_remove_cand :
    forall (l : list A) (a0 : A),
      vl (a0 :: l) <->
      vl l /\
      ((exists (a0' : A), In a0' l /\ forall (x : A), In x l -> (P a0 x <-> P a0' x) /\
                                                    (P x a0 <-> P x a0')) \/
       (forall (x : A), In x l -> P a0 x \/ P x a0)).
  Proof.
  Admitted.
    
   
  Lemma vl_or_notvl : forall l : list A, vl l \/ ~vl l.
  Admitted.

  Definition valid := exists (f : A -> nat), forall (c d : A), P c d <-> (f c < f d)%nat.

  Lemma from_vl_to_valid : forall l : list A, (forall a : A, In a l -> valid <-> vl l).
  Proof.
  Admitted.

  Lemma decidable_valid : finite -> {valid} + {~valid}.
  Proof.
  Admitted.

End Cand.




  
    
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
    
