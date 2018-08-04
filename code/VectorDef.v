Require Import ListLemma.

Notation "'existsT' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'existsT' '/ ' x .. y , '/ ' p ']'") : type_scope.
  
Module Vec.

  Require Import Coq.Vectors.VectorDef.
  Require Import Coq.Vectors.Vector.
  Require Import Coq.Numbers.Natural.Peano.NPeano.
  
 
  Fixpoint vtake {A : Type} (n : nat) (m : nat) : (n <= m)%nat -> Vector.t A m -> Vector.t A n.
    refine (match n as n' return (n' <= m)%nat -> Vector.t A m -> Vector.t A n' with
            | O => fun Hnm v => @nil A
            | S n' => fun Hnm v =>
                       match v in Vector.t _ m
                             return (S n' <= m)%nat -> Vector.t A (S n') with
                       | nil _ => fun H => False_rect _ (Nat.nle_succ_0 _ H) 
                       | cons _ h _ t => fun H => cons _ h _ (vtake _ _ _ (le_S_n _ _ H) t) 
                       end Hnm
            end).
  Defined.


  Fixpoint vdrop {A : Type} (n : nat) (m : nat) : (n <= m)%nat -> Vector.t A m -> Vector.t A (m - n).
    refine (match n as n' return n' = n -> (n' <= m)%nat -> Vector.t A m -> Vector.t A (m - n') with
            | O => fun Hn Hnm v => _
            | S n' =>
              fun Hn Hnm v =>
                match v in Vector.t _ m
                      return (S n' <= m)%nat -> Vector.t A m -> Vector.t A (m - S n') with
                | nil _ => fun H t => False_rect _ (Nat.nle_succ_0  _ H)
                | cons _ h _ t => fun Hnm' t => _
                end Hnm v 
            end eq_refl).
    rewrite (Nat.sub_0_r m); exact v.
    rewrite (Nat.sub_succ n0 n');
      pose proof (le_S_n _ _ Hnm') as H;
      exact (vdrop _ _ _ H t0).
  Defined.


  Fixpoint vvtake {A : Type} (n : nat) (m : nat) : Vector.t A (n + m) -> Vector.t A n.
    refine (match n as n' return n' = n -> Vector.t A (n' + m) -> Vector.t A n' with
            | O => fun Heq v => @nil A
            | S n' => fun Heq v =>
                       match v in Vector.t _ m'
                       return m' = (S n' + m)%nat -> Vector.t A m' -> Vector.t A (S n') with
                       | nil _ => fun H v => False_rect _ (Nat.neq_0_succ _ H)
                       | cons _ h _ t => fun H v => cons _ h _ (vvtake _ n' m _)
                       end eq_refl v
            end eq_refl).
    inversion H.  rewrite H1 in t.
    exact t.
  Defined.

           
  Fixpoint vvdrop {A : Type} (n : nat) (m : nat) : Vector.t A (n + m) -> Vector.t A m.
    refine (match n as n' return n' = n -> Vector.t A (n' + m) -> Vector.t A m with
            | O => fun Hn v => v
            | S n' =>
              fun Hn v =>
                match v in Vector.t _ m'
                      return m' = (S n' + m)%nat -> Vector.t A m' -> Vector.t A m with
                | nil _ => fun H _ => False_rect _ (Nat.neq_0_succ _ H) 
                | cons _ _ _ t => fun H v => vvdrop _ n' m _ 
                end eq_refl v
            end eq_refl).
    inversion H. rewrite H1 in t.
    exact t.
  Defined.


  Fixpoint matrix_from_vector {A : Type} (m : nat) (n : nat) :
    Vector.t A (m * n) -> Vector.t (Vector.t A n) m.
  Proof.
    refine (match m as m' return m' = m -> Vector.t A (m' * n) -> Vector.t (Vector.t A n) m' with
            | O => fun H v => @nil (Vector.t A n) 
            | S m' => fun H vec => _
            end eq_refl).
    simpl in vec.
    pose proof (vvtake n (m' * n) vec) as fn.
    pose proof (vvdrop n (m' * n) vec) as rn.
    pose proof (matrix_from_vector _ _ _ rn) as rt.
    exact (cons _ fn _ rt).
  Defined.
    
  Fixpoint to_matrix {A : Type} (m : nat) (n : nat) :
    Vector.t A (m * n) -> Vector.t (Vector.t A n) m.
  Proof.
    induction m; simpl; intros vec.
    - constructor.
    - constructor.
      +  pose proof (vvtake n (m * n) vec).
         exact X.
      +  pose proof (vvdrop n (m * n) vec).
         exact (IHm X).
  Defined.

  
  Fixpoint transpose_matrix {A : Type} (m : nat) (n : nat) :
    Vector.t (Vector.t A n) m -> Vector.t (Vector.t A m) n.
  Proof.
    induction n; simpl; intros mat.
    - constructor. 
    - remember (map hd mat) as h.
      remember (map tl mat) as r.
      exact (cons _ h _ (transpose_matrix _ _ _ r)).
  Defined.

  Fixpoint zip_vectors {A B C : Type} (f : A -> B -> C) (m : nat) :
    Vector.t A m -> Vector.t B m -> Vector.t C m.
    refine (match m as m' return m' = m -> Vector.t A m' -> Vector.t B m' -> Vector.t C m' with
            | O => fun H v1 v2 => @nil C
            | S m' => fun H v1 v2 =>
                     _
            end eq_refl).
    inversion v1; inversion v2; subst.
    exact (cons _ (f h h0) _ (zip_vectors _ _ _ f m' X X0)).
  Defined.

  
    
  Arguments cons {A} _ {n} _.
  Arguments nil {A}.

  Definition example : Vector.t nat (2 * 3) :=
    (cons 1 (cons 2 (cons 3 (cons 4 (cons 5 (cons 6 nil))))))%nat.

  Eval compute in matrix_from_vector _ _ example.
  Eval compute in to_matrix _ _ example.
  Eval compute in transpose_matrix _ _ (matrix_from_vector _ _ example).
  Eval compute in zip_vectors (fun x y => (x, y)) _ example example.
  
  
  
End Vec.


Lemma matrix_from_list :
  forall (A : Type) (l : list A) (n : nat) (H1 : List.length l = (n * n)%nat) (H2 : n <> O),
    existsT (v : list (list A)), List.concat v = l /\ List.length v = n /\
                                 List.length (List.hd nil v) = n.
Proof.
  intros A l n H1 H2.
  remember (Vector.of_list l) as v.
  (* After clearing Heqv, I can rewrite H1 in v, but I don't want to do that *
  clear Heqv. rewrite H1 in v. *)
  rewrite H1 in v. (* Getting error Error: Cannot change v, it is used in hypothesis Heqv. *)
  remember (Vec.matrix_from_vector _ _ v) as mt.
  