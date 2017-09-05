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


Section Choice.

  Require Import Coq.Logic.ChoiceFacts.
  
  Variable A : Type.
  Variable l : list A.
  Hypothesis finite : forall c : A, In c l.
  Hypothesis dec_A : forall n m : A, {n = m} + {n <> m}.
  Hypothesis l_not_nil : l <> nil.
  
  Definition valid (P : A -> A -> Prop) :=
    exists (f : A -> nat), forall c d,
        P c d <-> (f c < f d)%nat.
  
  Lemma dec_now : forall (P : A -> A -> Prop),
      (forall c d, P c d \/ ~P c d) ->
      {valid P} + {~valid P}.
  Proof.
    intros P H. unfold valid.
    Check ConstructiveIndefiniteDescription_on.
    Check (classical_denumerable_description_imp_fun_choice).
    
