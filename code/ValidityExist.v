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

  
  (* vl : forall A : Type, (P : A -> A -> Prop) -> (list A) -> Prop *)
  Definition vl (l : list A) :=
    exists (f : A -> nat), forall (c d : A),
        In c l -> In d l -> (if P c d =? -1 then (f d < f c)%nat
                           else  if P c d =? 0 then (f c = f d)%nat
                                 else  if P c d =? 1 then (f c < f d)%nat
                                       else False) /\
                          (if (f d <? f c)%nat then P c d = -1
                           else if (f c =? f d)%nat then P c d = 0
                                else  P c d = -1).
          