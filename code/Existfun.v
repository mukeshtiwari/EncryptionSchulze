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
  Variable A_all : list A.
  (* Hypothesis about A being finite, decidable and nonempty *)
  Hypothesis Afin : forall (a : A), In a A_all. 
  Hypothesis A_dec : forall (a b : A) , {a = b} + {a <> b}.
  Hypothesis A_not_nil : A_all <> nil.

  
  Definition valid (P : A -> A -> Prop) (l : list A) :=
    exists (f : A -> nat), forall c d (Hc : In c l) (Hd : In d l), (P c d <-> (f c < f d)%nat).

  Definition equal_rank (P : A -> A -> Prop) (c d : A) :=
     ~P c d /\ ~P d c.

 
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
    split. right. firstorder.
    exists f. split; intros. rewrite e in Hc, Hd.
    pose proof (H c d0). simpl in *. firstorder.
    rewrite e in Hc, Hd.
    pose proof (H c d0). simpl in *. firstorder.
    
    (* a <> d *)
    split. apply in_eq.
    split. pose proof (H a d (in_eq a l)). firstorder.
    split. admit. 
    exists f. split; intros. simpl in Hc, Hd. destruct (A_dec d a).
    symmetry in e. pose proof (n e). inversion H1.
    simpl in *. destruct Hc, Hd.  firstorder.
    pose proof (H c d0). firstorder.
    pose proof (H c d0). firstorder.
    pose proof (H c d0). firstorder.
    pose proof (H c d0). firstorder.
    
    (* reverse direction *)
    destruct H as [c H].

    induction l. firstorder.
   
    
  Lemma dec_now : forall (P : A -> A -> Prop),
      (forall c d, P c d \/ ~P c d) ->
      {valid P} + {~valid P}.
  Proof.
    intros P H. unfold valid.
    
