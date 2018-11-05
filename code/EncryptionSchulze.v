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
Require Import ValidityExist.
Import ListNotations.
Open Scope Z.

Notation "'existsT' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'existsT' '/ ' x .. y , '/ ' p ']'") : type_scope.

Section Encryption.

  Variable cand : Type.
  Variable cand_all : list cand.
  Hypothesis cand_fin : forall c: cand, In c cand_all.
  Hypothesis dec_cand : forall n m : cand, {n = m} + {n <> m}.
  Hypothesis cand_not_nil : cand_all <> nil.

 
  Section Evote.
    (** Section 2: Specification of Schulze Vote Counting **)

    (* marg is the margin in Schulze counting, i.e. marg c d is the number of
       voters that perfer c over d. The existence of the margin function
       is assumed for the specification of Schulze Voting and will be
       constructed from incoming ballots later *)
    Variable marg : cand -> cand -> Z.

    (* prop-level path *)
    Inductive Path (k: Z) : cand -> cand -> Prop :=
    | unit c d : marg c d >= k -> Path k c d
    | cons  c d e : marg c d >= k -> Path k d e -> Path k c e.

    (* winning condition of Schulze Voting *)
    Definition wins_prop (c: cand) := forall d: cand, exists k: Z,
          Path k c d /\ (forall l, Path l d c -> l <= k).

    (* dually, the notion of not winning: *)
    Definition loses_prop (c : cand) := exists k: Z, exists  d: cand,
          Path k d c /\ (forall l, Path l c d -> l < k).

    (** Section 3: A Scrutiny Sheet for the Schulze Method **)

    (* boolean function that determines whether the margin between a
       pair  of candidates is below a given integer *)
    Definition marg_lt (k : Z) (p : (cand * cand)) :=
      Zlt_bool (marg (fst p) (snd p)) k.

    (* definition of the (monotone) operator W_k that defines coclosed sets *)
    Definition W (k : Z) (p : cand * cand -> bool) (x : cand * cand) :=
      andb
        (marg_lt k x)
        (forallb (fun m => orb (marg_lt k (fst x, m)) (p (m, snd x))) cand_all).

    (* k-coclosed predicates *)
    Definition coclosed (k : Z) (p : (cand * cand) -> bool) :=
      forall x, p x = true -> W k p x = true.

    (* type-level path to replace prop-level path *)
    Inductive PathT (k: Z) : cand -> cand -> Type :=
    | unitT c d : marg c d >= k -> PathT k c d
    | consT c d e : marg c d >= k -> PathT k d e -> PathT k c e.

    (* type-level winning condition in Schulze counting *)
    Definition wins_type c :=
      forall d : cand, existsT (k : Z),
      ((PathT k c d) *
       (existsT (f : (cand * cand) -> bool), f (d, c) = true /\ coclosed (k + 1) f))%type.

    (* dually, the type-level condition for non-winners *)
    Definition loses_type (c : cand) :=
      existsT (k : Z) (d : cand),
      ((PathT k d c) *
       (existsT (f : (cand * cand) -> bool), f (c, d) = true /\ coclosed k f))%type.

    (* type-level notions of winning and losing are equivalent *)
    (* auxilary lemmas needed for the proof of equivalence     *)
    (* search for wins_prop_type and wins_type_prop for the    *)
    (* statement and proof of equivalence, dually for losing.  *)

    (* type-level paths allow to construct evidence for the existence of paths *)
    Lemma path_equivalence : forall c d k , PathT k c d -> Path k c d.
    Proof.
      refine
        (fix F c d k H {struct H}:=
           match H with
           | unitT _ cf df mrg => unit _ cf df mrg
           | consT _ cf df ef mrg t => cons _ cf df ef mrg (F _ _ _ t)
           end).
    Qed.

    (* mp stands for midpoint and the lemma below shows that for a pair of candidates (a, c)
       with x = (a, c) in W_k p, and a putative midpoint b, we have that marg a b < k or p b c. *)
    Lemma mp_log : forall (k : Z) (x : cand * cand) (p : cand * cand -> bool),
        (forallb (fun m => orb (marg_lt k (fst x, m)) (p (m, snd x))) cand_all) = true ->
        forall b, p (b, snd x) = true \/ marg (fst x) b < k.
    Proof.
      intros k x p H b.
      assert (Hin : In b cand_all) by  apply cand_fin.
      pose proof (proj1 (forallb_forall _ cand_all) H b Hin) as Hp. simpl in Hp.
      apply orb_true_iff in Hp; destruct Hp as [Hpl | Hpr]; destruct x as (a, c); simpl in *.
      + right; apply Zlt_is_lt_bool; auto.
      + left;auto.
    Qed.

    (* all elements (x, y) in a k-coclosed set can only be joined by a path of strenght < k *)
    Lemma coclosed_path : forall k f, coclosed k f -> forall s x y,
          Path s x y -> f (x, y) = true -> s < k.
    Proof.
      intros k f Hcc x s y p. induction p.

      (* unit path *)
      + intros Hin; specialize (Hcc (c, d) Hin); apply andb_true_iff in Hcc;
          destruct Hcc as [Hccl Hccr]; apply Zlt_is_lt_bool in Hccl; simpl in Hccl;  omega.

      (* non unit path *)
      + intros Hin; specialize (Hcc (c, e) Hin); apply andb_true_iff in Hcc;
          destruct Hcc as [Hccl Hccr]; unfold marg_lt in Hccl; simpl in Hccl.
        assert (Hmp : forall m, f (m, (snd (c, e))) = true \/ marg (fst (c, e)) m < k)
          by (apply mp_log; auto); simpl in Hmp.
        specialize (Hmp d). destruct Hmp; [intuition | omega].
    Qed.


    Definition listify (m : cand -> cand -> Z) :=
      map (fun s => (fst s, snd s, m (fst s) (snd s))) (all_pairs cand_all).



    Lemma in_pairs : forall a b, In a cand_all -> In b cand_all -> In (a, b) (all_pairs cand_all).
    Proof.
      intros a b H1 H2. apply all_pairsin; auto.
    Qed.


    Fixpoint linear_search (c d : cand) l :=
      match l with
      | [] => marg c d
      | (c1, c2, k) :: t =>
        match dec_cand c c1, dec_cand d c2 with
        | left _, left _ => k
        | _, _ => linear_search c d t
        end
      end.
 

    Theorem equivalent_m : forall c d m, linear_search c d (listify m) = m c d.
    Proof.
      unfold listify.  intros c d m.
      assert (H1 : forall c1 c2, In (c1, c2) (all_pairs cand_all)).
      intros c1 c2. apply in_pairs; auto.
      specialize (H1 c d).
      induction (all_pairs cand_all).
      + inversion H1.
      + simpl.
        destruct a as (a1, a2). simpl in *.
        destruct (dec_cand c a1).
        destruct (dec_cand d a2). subst. auto.
        destruct H1. inversion H. symmetry in H2. unfold not in n.
        specialize (n H2). inversion n.
        apply IHl. auto.
        destruct H1. inversion H. unfold not in n. symmetry in H1.
        specialize (n H1). inversion n.
        apply IHl. auto.
    Qed.




    Fixpoint M_old (n : nat) (c d : cand) : Z :=
      match n with
      | 0%nat => marg c d
      | S n' =>
        Z.max (M_old n' c d) (maxlist (map (fun x : cand => Z.min (marg c x) (M_old n' x d)) cand_all))
      end.

    (* M is the iterated margin function and maps a pair of candidates c, d to the
       strength of the strongest path of length at most (n + 1) *)

    Fixpoint MM n :=
      match n with
      | O => listify marg
      | S n' =>
        let uu := MM n' in
        listify (fun c d =>
                   let u := linear_search c d uu in
                   let t := maxlist
                              (map (fun x => Z.min (marg c x) (linear_search x d uu)) cand_all) in
                   Z.max u t)
      end.

    Definition M n : cand -> cand -> Z :=
      let l := MM n in
      fun c d => linear_search c d l.


    Lemma M_M_new_equal : forall n c d , M n c d = M_old n c d.
    Proof.
      induction n. unfold M. simpl. intros c d. rewrite equivalent_m. auto.
      intros c d.  unfold M in *. simpl. rewrite equivalent_m.
      assert (Ht: maxlist (map (fun x : cand => Z.min (marg c x) (linear_search x d (MM n))) cand_all) =
                  maxlist (map (fun x : cand => Z.min (marg c x) (M_old n x d)) cand_all)).
      apply f_equal.
      clear cand_not_nil. clear cand_fin.
      induction cand_all. auto. simpl. pose proof (IHn a d).
      rewrite H. apply f_equal. auto.
      rewrite Ht. rewrite IHn. auto.
    Qed.


    (* partial correctness of iterated margin function: if the strength M n c d
       of the strongest path of length <= n+1 between c and d is at least s, then
       c and d can be joined by a type-level path of this strength *)
    Theorem iterated_marg_patht : forall n s c d, M n c d >= s -> PathT s c d.
    Proof.
      induction n.
      intros s c d H. constructor. unfold M in *. simpl in *. rewrite equivalent_m in H. auto.
      intros s c d H. unfold M in *. simpl in H. rewrite equivalent_m in H.
      unfold Z.max in H.
      destruct (linear_search c d (MM n)
                              ?= maxlist (map (fun x : cand => Z.min (marg c x) (linear_search x d (MM n))) cand_all)).
      apply IHn. auto.
      apply max_of_nonempty_list_type in H. destruct H as [x [H1 H2]].
      apply z_min_lb in H2. destruct H2.
      specialize (IHn _ _ _ H0). specialize (consT _ _ _ _ H IHn); auto.
      apply cand_not_nil.  apply dec_cand. apply IHn. assumption.
    Defined.


    (* as type level paths induce prop-level paths, the same as above also holds for prop-level
       paths *)
    Lemma iterated_marg_path : forall (n : nat) (s : Z) (c d : cand),
        M n c d >= s -> Path s c d.
    Proof.
      intros n s c d Hm.
      apply path_equivalence. apply iterated_marg_patht with (n := n).
      assumption.
    Qed.

    (* existence of a a path between c and d of strength s gives an interate of the
       iterated margin function with value at least s *)
    Lemma path_iterated_marg : forall (s : Z) (c d : cand),
        Path s c d -> exists n, M n c d >= s.
    Proof.
      intros s c d H.  induction H.
      exists 0%nat. unfold M. simpl. rewrite equivalent_m. auto. destruct IHPath.
      exists (S x). unfold M in *. simpl.  rewrite equivalent_m. apply z_max_lb. right.
      apply max_of_nonempty_list.
      apply cand_not_nil. apply dec_cand. exists d.
      split. pose proof (cand_fin d). auto.
      apply z_min_lb. split. auto. auto.
    Qed.

    (* monotonicity of the iterated margin function *)
    Lemma monotone_M : forall (n m : nat) c d, (n <= m)%nat  -> M n c d <= M m c d.
    Proof.
      intros n m c d H.  induction H; simpl; try omega.
      apply Z.ge_le. unfold M at 1. simpl. rewrite equivalent_m.
      apply z_max_lb with (m := M m c d).
      left. omega.
    Qed.

    (* Here, we view paths as lists of candidates, and str computes the strength of
       a path relative to the given margin function *)
    Fixpoint str c l d :=
      match l with
      | [] => marg c d
      | (x :: xs) => Z.min (marg c x)  (str x xs d)
      end.

    (* the iterated margin function is correct relative to the length of a path *)
    Lemma path_len_iterated_marg : forall k c d s l,
        (length l <= k)%nat -> str c l d >= s -> M k c d >= s.
    Proof.
      induction k. intros. assert ((length l <= 0)%nat -> l = []).
      { destruct l. intros. reflexivity.
        simpl in *. inversion H. }
      specialize (H1 H). subst. simpl in *. unfold M in *. simpl. rewrite equivalent_m. auto.
      intros. simpl in *. destruct l. simpl in *.
      unfold M in *. simpl.

      rewrite equivalent_m. apply z_max_lb.
      left. apply IHk with []. simpl. omega. simpl. auto.
      simpl in *. apply z_min_lb in H0. destruct H0.
      unfold M in *.  simpl.
      rewrite equivalent_m.
      apply z_max_lb. right. apply max_of_nonempty_list.
      apply cand_not_nil. apply dec_cand. exists c0. split. specialize (cand_fin c0). trivial.
      apply z_min_lb. split.
      omega. apply IHk with l. omega. omega.
    Qed.

    (* characterisation of the iterated margin function in terms of paths *)
    Lemma iterated_marg_char: forall k c d s,
        M k c d >= s <-> exists (l : list cand), (length l <= k)%nat /\ str c l d >= s.
    Proof.
      split. generalize dependent s. generalize dependent d.
      generalize dependent c. induction k. simpl. intros. exists []. simpl. intuition.
      unfold M in *. simpl in H. rewrite equivalent_m in H. auto.

      simpl. intros. unfold M in *. simpl in H.

      rewrite equivalent_m in H.  pose proof (proj1 (z_max_lb (M k c d) _ s) H).
      destruct H0.
      specialize (IHk c d s H0). destruct IHk as [l [H1 H2]]. exists l. omega. clear H.
      pose proof
           (max_of_nonempty_list _ cand_all cand_not_nil dec_cand s
                                 (fun x : cand => Z.min (marg c x) (M k x d))).
      destruct H. clear H1. specialize (H H0). destruct H as [e [H1 H2]].
      pose proof (proj1 (z_min_lb _ _ s) H2). destruct H.
      specialize (IHk e d s H3). destruct IHk as [l [H4 H5]].
      exists (e :: l). simpl. split. omega.
      apply z_min_lb. intuition.
      (* otherway *)
      intros. destruct H as [l [H1 H2]].
      pose proof (path_len_iterated_marg k c d s l H1 H2). omega.
    Qed.

    (* every path of strength >= s can be split into two paths of strength >= s *)
    Lemma path_split: forall c d a l1 l2 s,
        str c (l1 ++ a :: l2) d >= s <-> str c l1 a >= s /\ str a l2 d >= s.
    Proof.
      split. generalize dependent s. generalize dependent l2.
      generalize dependent a. generalize dependent d. generalize dependent c.
      induction l1; simpl; intros.
      apply z_min_lb in H. auto. apply z_min_lb in H. destruct H.
      assert ((marg c a) >= s /\ (str a l1 a0) >= s /\ str a0 l2 d >= s ->
              Z.min (marg c a) (str a l1 a0) >= s /\ str a0 l2 d >= s).
      { intros. destruct H1 as [H1 [H2 H3]]. split. apply z_min_lb. auto. auto. }
      apply H1. split. assumption. apply IHl1. assumption.
      (* other part *)
      generalize dependent s. generalize dependent l2.
      generalize dependent a. generalize dependent d. generalize dependent c.
      induction l1; simpl; intros. apply z_min_lb. auto.
      apply z_min_lb. destruct H. apply z_min_lb in H. destruct H.
      split. auto. apply IHl1. auto.
    Qed.

    (* cutting out a loop from a path does not decrease its strength *)
    Lemma path_cut: forall c d a l l1 l2 l3 s,
        l = l1 ++ a :: l2 ++ a :: l3 -> str c l d >= s -> str c (l1 ++ a :: l3) d >= s.
    Proof.
      intros. subst. apply path_split in H0. destruct H0.
      apply path_split in H0. destruct H0.
      pose proof (proj2 (path_split c d a l1 l3 s) (conj H H1)). auto.
    Qed.

    (* the iterated margin function stabilizes after n iterations, where n is the
       number of candidates. *)
    Lemma iterated_marg_stabilises: forall k n c d (Hn: (length cand_all = n)%nat),
        M (k + n) c d <= M n  c d.
    Proof.
      induction k using (well_founded_induction lt_wf). intros n c d Hn.
      remember (M (k + n) c d) as s.
      pose proof (Z.eq_le_incl _ _ Heqs). apply Z.le_ge in H0.
      pose proof (proj1 (iterated_marg_char _ _ _ _) H0). destruct H1 as [l [H1 H2]].
      (* number of candidates <= length Evote.cand_all \/ > length Evote.cand_all *)
      assert ((length l <= n)%nat \/ (length l > n)%nat) by omega.
      destruct H3 as [H3 | H3].
      pose proof (proj2 (iterated_marg_char n c d s)
                        (ex_intro (fun l => (length l <= n)%nat /\ str c l d >= s) l (conj H3 H2))). omega.
      (* length l > length Evote.cand_all and there are candidates. Remove the duplicate
         candidate *)
      rewrite <- Hn in H3. assert (covers cand cand_all l).
      { unfold covers. intros. pose proof (cand_fin x). assumption. }
      pose proof (list_split_dup_elem _ n cand_all dec_cand Hn l H3 H4).
      destruct H5 as [a [l1 [l2 [l3 H5]]]].
      pose proof (path_cut  _ _ _ _ _ _ _ _ H5 H2).
      remember (l1 ++ a :: l3) as l0.
      assert ((length l0 <= n)%nat \/ (length l0 > n)%nat) by omega.
      destruct H7.
      pose proof (iterated_marg_char n c d s). destruct H8.
      assert ((exists l : list cand, (length l <= n)%nat /\ str c l d >= s)).
      exists l0. intuition. specialize (H9 H10).  omega.
      rewrite Hn in H3.
      specialize (list_and_num _ _ _ H3); intros. destruct H8 as [p H8].
      specialize (list_and_num _ _ _ H7); intros. destruct H9 as [k' H9].
      assert ((length l0 < length l)%nat).
      { rewrite Heql0, H5.
        rewrite app_length. rewrite app_length.
        simpl. rewrite app_length. simpl.
        omega. }
      rewrite H9 in H10. rewrite H8 in H10.
      assert (((k' + n) < (p + n))%nat -> (k' < p)%nat) by omega.
      specialize (H11 H10). assert (k' < k)%nat by omega.
      specialize (H k' H12 n c d Hn).
      pose proof (iterated_marg_char (length l0) c d (str c l0 d)).
      destruct H13.
      assert ((exists l : list cand, (length l <= length l0)%nat /\ str c l d >= str c l0 d)).
      { exists l0. omega. }
      specialize (H14 H15). clear H13. rewrite <- H9 in H. omega.
    Qed.

    (* the iterated margin function reaches a fixpoint after n iterations, where
       n is the number of candidates *)
    Lemma iterated_marg_fp : forall (c d : cand) (n : nat),
        M n c d <= M (length cand_all) c d.
    Proof.
      intros c d n. assert ((n <= (length cand_all))%nat \/
                            (n >= (length cand_all))%nat) by omega.
      destruct H. apply monotone_M. assumption.
      remember ((length cand_all)) as v.
      assert ((n >= v)%nat -> exists p, (n = p + v)%nat).
      { intros. induction H. exists 0%nat. omega.
        assert ((v <= m)%nat -> (m >= v)%nat) by omega.
        specialize (H1 H). specialize (IHle H1). destruct IHle as [p H2].
        exists (S p). omega. }
      specialize (H0 H). destruct H0 as [p H0].
      subst. apply  iterated_marg_stabilises. auto.
    Qed.

    (* boolean valued function that determines election winners based on the
       (fixpoint of the) iterated margin function *)
    Definition c_wins c :=
      forallb (fun d => (M (length cand_all) d c) <=? (M (length cand_all) c d))
              cand_all.
    (* characterisation of c_wins returning true in terms of iterated margin function *)
    Lemma c_wins_true (c : cand) :
      c_wins c = true <-> forall d, M (length cand_all) d c <= M (length cand_all) c d.
    Proof.
      split; intros.
      unfold c_wins in H.
      pose proof
           (proj1 (forallb_forall
                     (fun d : cand => M (length cand_all) d c <=?
                                      M (length cand_all) c d) cand_all) H).
      pose proof (H0 d (cand_fin d)). simpl in H1.
      apply Zle_bool_imp_le. assumption.
      unfold c_wins. apply forallb_forall. intros x Hin.
      pose proof H x. apply Zle_imp_le_bool. assumption.
    Qed.

    (* characterisation of c_wins returning false in terms of the interated margin function *)
    Lemma c_wins_false (c : cand):
      c_wins c = false <-> exists d, M (length cand_all) c d < M (length cand_all) d c.
    Proof.
      split; intros. unfold c_wins in H.
      apply forallb_false in H. destruct H as [x [H1 H2]].
      exists x. apply Z.leb_gt in H2. omega.
      destruct H as [d H]. unfold c_wins. apply forallb_false.
      exists d. split. pose proof (cand_fin d). assumption.
      apply Z.leb_gt. omega.
    Qed.


    (* the propositional winning condition implies winning in terms of the interated margin
       function *)
    Lemma wins_prop_iterated_marg (c : cand): wins_prop c ->
                                              forall d, M (length cand_all) d c <= M (length cand_all) c d.
    Proof.
      intros. specialize (H d). destruct H as [k [H1 H2]].
      remember (M (length cand_all) d c) as s.
      apply Z.eq_le_incl in Heqs.
      apply Z.le_ge in Heqs.
      pose proof (iterated_marg_path _ _ _ _ Heqs). specialize (H2 s H).
      apply  path_iterated_marg in H1. destruct H1 as [n H1].
      pose proof (iterated_marg_fp c d n). omega.
    Qed.

    (* winning in terms of the iterated margin function gives the type-level winning condition *)
    Lemma iterated_marg_wins_type (c : cand): (forall d,
                                                  M (length cand_all) d c <= M (length cand_all) c d) ->
                                              wins_type c.
    Proof.
      (* rewrite it using refine tactic *)

      intros H d. specialize (H d).
      remember (M (length cand_all) c d) as s eqn:Heqs.
      apply Z.eq_le_incl in Heqs.
      apply Z.le_ge in Heqs. exists s.
      pose proof (iterated_marg_patht _ _ _ _ Heqs) as Hi.
      split.
      - intuition.
      - remember (M (length cand_all) d c) as r eqn:Heqr.
        exists (fun x => M (length cand_all) (fst x) (snd x) <=? r).
        split.
        + apply Z.leb_le. simpl. intuition.
        + intros x Hx. destruct x as (x, z).
          apply Z.leb_le in Hx. apply andb_true_iff.
          split.
          * apply Z.ltb_lt. simpl in *.
            clear Heqs. clear Heqr.
            induction (length cand_all); simpl in Hx. unfold M in Hx. simpl in Hx.
            rewrite equivalent_m in Hx.
            intuition.
            apply IHn. unfold M in Hx. simpl in Hx.
            rewrite equivalent_m in Hx.  apply Z.max_lub_iff in Hx. intuition.
          * apply forallb_forall. intros y Hy. apply orb_true_iff.
            simpl in *.
            assert (A : marg x y <= s \/ marg x y > s) by omega.
            destruct A as [A1 | A2].
            left. apply Z.ltb_lt. simpl. omega.
            right. apply Z.leb_le.
            assert (B : M (length cand_all) y z <= r \/ M (length cand_all) y z >= r + 1) by omega.
            destruct B as [B1 | B2].
            intuition.
            apply iterated_marg_path in B2.
            assert (A3 : marg x y >= r + 1) by omega.
            pose proof (cons _ _ _ _ A3 B2) as C.
            apply  path_iterated_marg in C. destruct C as [n C].
            pose proof (iterated_marg_fp x z n). omega.
    Defined.



    (* the type level winning condition can be reconstruced from *)
    (* propositional knowledge of winning *)
    Lemma wins_prop_type : forall c, wins_prop c -> wins_type c.
    Proof.
      intros c H. unfold wins_prop, wins_type in *.
      apply iterated_marg_wins_type. apply wins_prop_iterated_marg. auto.
    Qed.

    (* dually, the type-level information witnessing winners *)
    (* entails prop-level knowledge. *)
    Lemma wins_type_prop : forall c, wins_type c -> wins_prop c.
    Proof.
      intros c H. unfold wins_prop, wins_type in *. intros d.
      destruct (H d) as [k [H1 [f [H3 H4]]]].
      exists k. split. apply path_equivalence. auto.
      intros l H5. pose proof (coclosed_path _ _ H4).
      pose proof (H0 l _ _ H5 H3). omega.
    Qed.

    (* the losing condition in terms of the iterated margin function *)
    Lemma loses_prop_iterated_marg (c : cand):
      loses_prop c ->
      (exists d, M (length cand_all) c d < M (length cand_all) d c).
    Proof.
      intros. destruct H as [k [d [H1 H2]]].
      exists d. remember (M (length cand_all) c d)  as s.
      pose proof (Z.eq_le_incl _ _ Heqs) as H3.
      apply Z.le_ge in H3. apply iterated_marg_path in H3. specialize (H2 s H3).
      apply  path_iterated_marg in H1. destruct H1 as [n H1].
      pose proof (iterated_marg_fp d c n). omega.
    Qed.

    (* existential quantifiers over finite lists can be reified into Sigma-types for
       decidable properties *)
    Definition exists_fin_reify {A: Type} (P: A -> Prop):
      (forall a: A, {P a} + {~(P a)}) ->
      forall l: list A, (exists a, In a l /\ P a) -> existsT a, P a :=
      fun Pdec =>
        fix F l {struct l} :=
        match l  as m return ((exists a : A, In a m /\ P a) -> existsT a : A, P a) with
        | [] =>
          fun H : exists a : A, In a [] /\ P a =>
            (fun Hf : False => (fun X : existsT a : A,P a => X)
                                 match Hf return
                                       (existsT a : A,P a) with end)
              match H with
              | ex_intro _ a (conj Ha _) => (fun H1 : False => H1) match Ha return False with end
              end
        | h :: t => fun H =>
                      match (Pdec h) with
                      | left e => existT _ h e
                      | right r =>
                        F t
                          match H with
                          | ex_intro _ a (conj (or_introl e) Hpa) =>
                            (fun rr : ~ P a => False_ind (exists a1 : A, In a1 t /\ P a1) (rr Hpa))
                              (eq_ind h (fun hh : A => ~ P hh) r a e)
                          | ex_intro _ a (conj (or_intror rr as Hin) Hpa as a0) =>
                            ex_intro _ a (conj rr Hpa)
                          end
                      end
        end.

    (* reification of candidates given propositional existence *)
    Corollary reify_opponent (c: cand):
      (exists  d, M  (length cand_all) c d < M (length cand_all) d c) ->
      (existsT d, M  (length cand_all) c d < M (length cand_all) d c).
      refine (fun Hex  =>
                (fun Hdec : forall d : cand,
                     {M (length cand_all) c d < M (length cand_all) d c} +
                     {~ M (length cand_all) c d < M (length cand_all) d c} =>
                   exists_fin_reify
                     _  Hdec cand_all
                     match Hex with
                     | ex_intro _ d Hex0 =>
                       ex_intro _ d (conj (cand_fin d) Hex0)
                     end)
                  (fun d : cand =>
                     let s := Z_lt_ge_bool (M (length cand_all) c d) (M (length cand_all) d c) in
                     let (b, P) := s in
                     (if b as bt
                         return
                         ((if bt
                           then M (length cand_all) c d < M (length cand_all) d c
                           else M (length cand_all) c d >= M (length cand_all) d c) ->
                          {M (length cand_all) c d < M (length cand_all) d c} +
                          {~ M (length cand_all) c d < M (length cand_all) d c})
                      then fun Pt => left Pt
                      else fun Pf => right (fun H => Pf H)) P)).
    Defined.



    (* reconstructon of the losing condition type-level losing from interated
       margin function *)
    Lemma iterated_marg_loses_type (c : cand) :
      (exists d, M (length cand_all) c d < M (length cand_all) d c) -> loses_type c.
    Proof.
      unfold loses_type. intros.
      assert (HE:  existsT d, M  (length cand_all) c d < M (length cand_all) d c).
      apply reify_opponent. assumption.
      destruct HE as [d HE].
      remember (M (length cand_all) d c) as s. exists s, d.
      split. assert (H1 : M (length cand_all) d c >= s) by omega.
      apply iterated_marg_patht in H1. auto.
      exists (fun x => M (length cand_all) (fst x) (snd x) <? s).
      simpl in *. split. apply Z.ltb_lt. omega.
      unfold coclosed. intros x; destruct x as (x, z); simpl in *.
      intros. apply Z.ltb_lt in H0. unfold W.
      apply andb_true_iff. split. unfold marg_lt. simpl. apply Z.ltb_lt.
      clear H. clear Heqs.
      induction (length cand_all). unfold M in *. simpl in *.  rewrite equivalent_m in H0.  omega.
      unfold M in H0.
      simpl in H0. rewrite equivalent_m in H0.
      apply Z.max_lub_lt_iff in H0. destruct H0. apply IHn. auto.
      unfold M in HE.
      simpl in HE. rewrite equivalent_m in HE.
      apply Z.max_lub_lt_iff in HE. destruct HE as [H1 H2]. assumption. assumption.

      apply forallb_forall. intros y Hy.
      apply orb_true_iff. unfold marg_lt. simpl.
      assert (marg x y < s \/ marg x y >= s) by omega.
      destruct H1. left. apply Z.ltb_lt. auto.
      right. apply Z.ltb_lt.
      assert (M (length cand_all) y z < s \/ M (length cand_all) y z >= s) by omega.
      destruct H2. auto.
      apply iterated_marg_path in H2.  pose proof (Evote.cons _ _ _ _ H1 H2).
      apply  path_iterated_marg in H3. destruct H3 as [n H3].
      pose proof (iterated_marg_fp x z n). omega.
    Defined.

    (* prop-level losing implies type-level losing *)
    Lemma loses_prop_type : forall c, loses_prop c -> loses_type c.
    Proof.
      intros c H. unfold loses_prop, loses_type in *. apply iterated_marg_loses_type.
      apply loses_prop_iterated_marg. auto.
    Qed.

    (* type-level losing implies prop-level losing *)
    Lemma loses_type_prop : forall c, loses_type c -> loses_prop c.
    Proof.
      intros c H. unfold loses_prop, loses_type in *.
      destruct H as [k [d [Hp [f [Hf Hc]]]]].
      exists k, d. split. apply path_equivalence. auto.
      intros l H. pose proof (coclosed_path k f Hc).
      pose proof (H0 l _ _ H Hf). omega.
    Qed.

    (* decidability of type-level winning *)
    Lemma wins_loses_type_dec : forall c, (wins_type c) + (loses_type c).
    Proof.
      intros c. destruct (c_wins c) eqn : c_wins_val.  left.
      unfold wins_type. apply  iterated_marg_wins_type. apply wins_prop_iterated_marg. intros d.
      pose proof (proj1 (forallb_forall _ cand_all) c_wins_val d (cand_fin d)).
      simpl in H. apply Zle_bool_imp_le in H. apply Z.le_ge in H.
      remember (M (length cand_all) d c) as s. apply iterated_marg_path in H.
      exists s. split. assumption.
      intros. rewrite Heqs. apply  path_iterated_marg in H0. destruct H0 as [n H0].
      apply Z.ge_le in H0. pose proof (iterated_marg_fp d c n). omega.
      right. apply iterated_marg_loses_type. unfold c_wins in c_wins_val.
      apply forallb_false_type in c_wins_val.
      destruct c_wins_val as [d [H1 H2]]. apply Z.leb_gt in H2. exists d. auto.
    Defined.

    (* aligning c_wins with type level evidence *)
    Lemma c_wins_true_type:
      forall c : cand, c_wins c = true <-> (exists x : wins_type c, wins_loses_type_dec c = inl x).
    Proof.
      split; intros. destruct (wins_loses_type_dec c) eqn:Ht. exists w. auto.
      pose proof (loses_type_prop c l). unfold loses_prop in H0.
      apply loses_prop_iterated_marg  in H0.
      pose proof (proj1 (c_wins_true c) H). destruct H0. specialize (H1 x). omega.
      destruct H. pose proof (wins_type_prop c x). unfold wins_prop in H0.
      apply c_wins_true. apply wins_prop_iterated_marg. auto.
    Qed.

    (* aligning of c_wins with losing condition *)
    Lemma c_wins_false_type:
      forall c : cand, c_wins c = false <-> (exists x : loses_type c, wins_loses_type_dec c = inr x).
    Proof.
      split; intros. destruct (wins_loses_type_dec c) eqn:Ht.
      pose proof (wins_type_prop c w).
      pose proof (proj1 (c_wins_false c) H). unfold wins_prop in H0.
      pose proof (wins_prop_iterated_marg c H0). destruct H1. specialize (H2 x). omega.
      exists l. auto.
      destruct H. pose proof (loses_type_prop c x). unfold loses_prop in H0.
      apply c_wins_false. apply loses_prop_iterated_marg. auto.
    Qed.


  End Evote.

  
  Section  Count.

    Definition ballot := cand -> nat.

    Inductive State: Type :=
    | partial: (list ballot * list ballot)  -> (cand -> cand -> Z) -> State
    | winners: (cand -> bool) -> State.

    Inductive Count (bs : list ballot) : State -> Type :=
    | ax us m : us = bs -> (forall c d, m c d = 0) ->
                Count bs (partial (us, []) m)             (* zero margin      *)
    | cvalid u us m nm inbs : Count bs (partial (u :: us, inbs) m) ->
                              (forall c, (u c > 0)%nat) ->              (* u is valid       *)
                              (forall c d : cand,
                                  ((u c < u d)%nat -> nm c d = m c d + 1) (* c preferred to d *) /\
                                  ((u c = u d)%nat -> nm c d = m c d)     (* c, d rank equal  *) /\
                                  ((u c > u d)%nat -> nm c d = m c d - 1))(* d preferred to c *) ->
                              Count bs (partial (us, inbs) nm)
    | cinvalid u us m inbs : Count bs (partial (u :: us, inbs) m) ->
                             (exists c, (u c = 0)%nat)                 (* u is invalid     *) ->
                             Count bs (partial (us, u :: inbs) m)
    | fin m inbs w (d : (forall c, (wins_type m c) + (loses_type m
                                                            c))):
        Count bs (partial ([], inbs) m)           (* no ballots left  *) ->
        (forall c, w c = true <-> (exists x, d c = inl x)) ->
        (forall c, w c = false <-> (exists x, d c = inr x)) ->
        Count bs (winners w).

    Open Scope nat_scope.

    Definition forall_exists_fin_dec : forall (A : Type) (l : list A) (f : A -> nat),
        {forall x, In x l -> f x > 0} + {exists x, In x l /\ f x = 0} := 
      fun (A : Type) =>
        fix F l f {struct l} :=
        match l with
        | [] => left (fun (x : A) (H : In x []) => match H with end)
        | h :: t =>
          match Nat.eq_dec (f h) 0 with
          | left e =>
            right (ex_intro _  h (conj (in_eq h t) e))
          | right n =>
            match F t f with
            | left Fl =>
              left (fun x H =>
                      match H with
                      | or_introl H1 =>
                        match zerop (f x) with
                        | left e =>
                          False_ind (f x > 0) ((eq_ind h (fun v : A => f v <> 0) n x H1) e)
                        | right r => r
                        end
                      | or_intror H2 => Fl x H2
                      end)
            | right Fr =>
              right
                match Fr with
                | ex_intro _ x (conj Frl Frr) =>
                  ex_intro _ x (conj (in_cons h x t Frl) Frr)
                end
            end
          end
        end.

    Definition ballot_valid_dec : forall b : ballot, {forall c, b c > 0} + {exists c, b c = 0} :=
      fun b => let H := forall_exists_fin_dec cand cand_all in
               match H b with
               | left Lforall => left
                                   (fun c : cand => Lforall c (cand_fin c))
               | right Lexists => right
                                    match Lexists with
                                    | ex_intro _ x (conj _ L) =>
                                      ex_intro (fun c : cand => b c = 0) x L
                                    end
               end.

    Open Scope Z_scope.

    Definition update_marg (p : ballot) (m : cand -> cand -> Z) : cand -> cand -> Z :=
      fun c d =>  if (Nat.ltb (p c) (p d))%nat
               then (m c d + 1)%Z
               else (if (Nat.ltb (p d) (p c))%nat
                     then (m c d -1)%Z
                     else m c d).

    Definition listify_v (m : cand -> cand -> Z) :=
      map (fun s => (fst s, snd s, m (fst s) (snd s))) (all_pairs cand_all). 


    Fixpoint linear_search_v (c d : cand) (m : cand -> cand -> Z) l :=
      match l with
      | [] => m c d
      | (c1, c2, k) :: t =>
        match dec_cand c c1, dec_cand d c2 with
        | left _, left _ => k
        | _, _ => linear_search_v c d m t
        end
      end.
    
   

    

    Definition update_marg_listify (p : ballot) (m : cand -> cand -> Z) : cand -> cand -> Z :=
      let t := update_marg p m in
      let l := listify_v t in
      fun c d => linear_search_v c d t l.

    Theorem equivalent_m_w_v : forall c d m, linear_search_v c d m (listify_v m) = m c d.
    Proof.
      unfold  listify_v.
      intros. induction (all_pairs cand_all); simpl; auto.
      destruct a as (a1, a2). simpl in *.
      destruct (dec_cand c a1).
      destruct (dec_cand d a2). subst. auto.
      auto. auto.
    Qed.

    Corollary equiv_cor : forall p m c d, update_marg p m c d = update_marg_listify p m c d.
    Proof.
      intros p m c d.  unfold update_marg_listify.
      rewrite <- equivalent_m_w_v. 
      auto.      
    Qed.
      
    (* correctness of update_marg above *)
    Lemma update_marg_corr: forall m (p : ballot) (c d : cand),
        ((p c < p d)%nat -> update_marg p m c d = m c d + 1) /\
        ((p c = p d)%nat -> update_marg p m c d = m c d) /\
        ((p c > p d)%nat -> update_marg p m c d = m c d - 1).
    Proof.
      intros m p c d.
      split; intros; unfold update_marg.
      destruct (p c <? p d)%nat eqn: H1. omega.
      destruct (p d <? p c)%nat eqn: H2. apply Nat.ltb_lt in H2.
      apply Nat.ltb_ge in H1. omega.
      apply Nat.ltb_ge in H2. apply Nat.ltb_ge in H1. omega.
      split; intros.
      destruct (p c <? p d)%nat eqn: H1.
      apply Nat.ltb_lt in H1. omega.
      apply Nat.ltb_ge in H1. destruct (p d <? p c)%nat eqn: H2. apply Nat.ltb_lt in H2.
      apply Nat.ltb_ge in H1. omega. apply Nat.ltb_ge in H2. omega.
      unfold update_marg.
      destruct (p c <? p d)%nat eqn:H1. apply Nat.ltb_lt in H1. omega.
      apply Nat.ltb_ge in H1. destruct (p d <? p c)%nat eqn: H2.
      apply Nat.ltb_lt in H2. omega. apply Nat.ltb_ge in H2. omega.
    Qed.

    
     Lemma update_marg_corr_listify: forall m (p : ballot) (c d : cand),
        ((p c < p d)%nat -> update_marg_listify p m c d = m c d + 1) /\
        ((p c = p d)%nat -> update_marg_listify p m c d = m c d) /\
        ((p c > p d)%nat -> update_marg_listify p m c d = m c d - 1).
     Proof.
       intros m p c d. rewrite <- equiv_cor. apply update_marg_corr.
     Qed.


     Definition partial_count_all_counted bs : forall u inbs m,
        Count bs (partial (u, inbs) m) ->  existsT i m, (Count bs (partial ([], i) m)) :=
      fix F u {struct u} :=
        match u with
        | [] =>
          fun inbs m Hc =>
            existT _ inbs (existT _ m Hc)
        | h :: t =>
          fun inbs m Hc =>
            match ballot_valid_dec h with
            | left Hv =>
              let w := update_marg_listify h m in 
              F t inbs w (cvalid bs h t m w inbs Hc Hv (update_marg_corr_listify m h))
            | right Hi =>  F t (h :: inbs) m (cinvalid bs h t m inbs Hc Hi)
            end
        end.


    Definition all_ballots_counted (bs : list ballot) :
      existsT i m, Count bs (partial ([], i) m) :=
      partial_count_all_counted bs bs [] (fun _ _ : cand => 0)
                                (ax bs bs (fun _ _ : cand => 0) eq_refl
                                    (fun _ _ : cand => eq_refl)).


     Definition schulze_winners (bs : list ballot) :
      existsT (f : cand -> bool), Count bs (winners f) :=
      let (i, t) := all_ballots_counted bs in
      let (m, p) := t in
      existT  _ (c_wins m) (fin _ _ _ _ (wins_loses_type_dec m) p
                                (c_wins_true_type m) (c_wins_false_type m)).
     

  End Count.
  

    
  Require Import Coq.Strings.String.
  Require Import Coq.Logic.FinFun.
  Require Import Coq.Program.Basics.
  Section ECount.

    
    (*Relation between Public and Private key. Although it won't change the proof
      because we are not generating the keys in our code, and assuming it, but it's 
      still nice to have the relation *)

    (* Plain text *)
    Definition plaintext := Z.
    
    (* Cipher text is pair (c1, c2). Elgamal encryption *)
    Definition ciphertext := (Z * Z)%type.

    (* ballot is plain text value *)
    Definition pballot := cand -> cand -> plaintext.
    
    (* eballot is encrypted value *)
    Definition eballot := cand -> cand -> ciphertext.

      
    (* Group Definition in Elgamal *)
    Axiom Prime : Type. 
    Axiom Generator : Type.
    Axiom Pubkey : Type.
    Axiom Prikey : Type.
     

    (* private and public key *)
    Axiom prime : Prime.
    Axiom gen : Generator.
    Axiom privatekey : Prikey.
    Axiom publickey : Pubkey.

    Inductive Group : Type :=
      group : Prime -> Generator -> Pubkey -> Group.
    
    (* This function encrypts the message *)
    Axiom encrypt_message :
      Group ->  plaintext -> ciphertext.

    (* This function decrypts the message *)
    Axiom decrypt_message :
      Group -> Prikey -> ciphertext -> plaintext.

    (* Decryption is deterministic *)
    Axiom decryption_deterministic :
      forall (grp : Group) (privatekey : Prikey) (pt : plaintext),
      decrypt_message grp privatekey (encrypt_message grp pt) = pt.
    
    (* This function returns zero knowledge proof of encrypted message (c1, c2) *)
    Axiom construct_zero_knowledge_decryption_proof :
      Group -> Prikey -> ciphertext -> string.

    (* This function verifies the zero knowledge proof of plaintext, m, is honest decryption 
       of ciphertext *)
    Axiom verify_zero_knowledge_decryption_proof :
      Group -> plaintext -> ciphertext -> string -> bool.
 
    (* Axiom about honest decryption zero knowledge proof *)
    Axiom verify_true :
      forall (grp : Group) (pt : plaintext) (ct : ciphertext) (privatekey : Prikey)
        (H : pt = decrypt_message grp privatekey ct),
        verify_zero_knowledge_decryption_proof
          grp pt ct
          (construct_zero_knowledge_decryption_proof grp privatekey ct) = true.
    
    
 
      
    
    Definition Permutation := existsT (pi : cand -> cand), (Bijective pi).
    Axiom Commitment : Type.
    Axiom ZKP : Type.
    Axiom S : Type. 

    (* The idea is for each ballot u, we are going to count 
       we generate pi, cpi, and zkpcpi. We call row permute function 
       u and pi and it returns v. Then We call column permutation 
       on v and pi and it returns w. We decryp w as b with zero knowledge
       proof. *)

    (* We call a java function which returns permutation. Basically java function returns 
       array which is converted back to function in OCaml land*)
    Axiom generatePermutation :
      Group -> (* group *)
      nat -> (* length  *)
      Permutation.   
    

    (* Generate randomness used in permutation commitment. 
       Tuple s = pcs.getRandomizeSpace().getrandomElement() *)
    Axiom generateS : Group -> nat -> S.
    
    (* Pass the permutation and randomness, it returns commitment. The S used here 
       will be used in zero knowledge proof *)
    Axiom generatePermutationCommitment :
      Group -> (* group *)
      nat -> (* length *) 
      Permutation -> (* pi *)
      S -> (*randomness *)
      Commitment. (* cpi *)

    (* This function takes Permutation Commitment and S and returns ZKP *)
    Axiom zkpPermutationCommitment :
      Group -> (* group *)
      nat -> (* length *)
      Permutation -> (* pi *)
      Commitment -> (* cpi *)
      S -> (* randomness *)
      ZKP.
      
    Axiom verify_permutation_commitment :
      Group -> (* group *)
      nat -> (* length *)
      Commitment -> (* cpi *)
      ZKP -> (* zero knowledge proof *)
      bool. (* pcps.verify offlineProof offlinePublicInpu *)

    
    Axiom permutation_commitment_axiom :
      forall (grp : Group) (pi : Permutation) (cpi : Commitment) (s : S)
        (zkppermcommit : ZKP)
        (H0 : s = generateS grp (List.length cand_all))
        (H1 : cpi = generatePermutationCommitment grp (List.length cand_all) pi s)
        (H2 : zkppermcommit = zkpPermutationCommitment
                                grp (List.length cand_all) pi cpi s),
        verify_permutation_commitment grp (List.length cand_all)
                                      cpi zkppermcommit = true.
    
    Axiom homomorphic_addition :
      Group -> ciphertext -> ciphertext -> ciphertext.
    
    (* Property of Homomorphic addition *)
    Axiom homomorphic_addition_axiom :
      forall (grp : Group) (c d : ciphertext),
        decrypt_message grp privatekey (homomorphic_addition grp c d) =
        decrypt_message grp privatekey c + decrypt_message grp privatekey d.    
    
    (* Start of Shuffle code *)     
    Axiom R : Type.
   
    (* Generate Randomness R separately *)
    Axiom generateR : Group -> nat -> R. (* Group and length *) 
    
    (* Changing each row from list cipertext to function type because easy to finish the proof *)
    Axiom shuffle :
      Group -> (* group *)
      nat -> (* I don't need this length but keep it for the moment and remove it in the end *)
      (cand -> ciphertext) -> (* ciphertext *)
      Permutation -> (* pi *)
      R -> (* Randomness R *)
      (cand -> ciphertext).
    
    (* Construct zero knowledge proof from original and shuffled ballot *)   
    (* Each row of ballot is represented by function *)
    Axiom shuffle_zkp :
      Group -> (* group *)
      nat -> (* length *)
      (cand -> ciphertext) -> (* cipertext *)
      (cand -> ciphertext) -> (* shuffle cipertext *)
      Permutation -> (* pi *)
      Commitment -> (* cpi *)
      S -> (* s, permutation commitment randomness *)
      R -> (* r, shuffle randomness *)
      ZKP. (* zero knowledge proof of shuffle *)
    
    (* verify shuffle *)
    Axiom verify_shuffle:
      Group -> (* group *)
      nat -> (* length *)
      (cand -> ciphertext) -> (* cipertext *)
      (cand -> ciphertext) -> (* shuffled cipertext *)
      Commitment -> (* permutation commitment *)
      ZKP -> (* zero knowledge proof of shuffle *)
      bool. (* true or false *)
     
    (* Changed data structure *)
    Axiom verify_shuffle_axiom :
      forall (grp : Group) (pi : Permutation) (cpi : Commitment) (s : S)
        (cp shuffledcp : cand -> ciphertext)
        (r : R) (zkprowshuffle : ZKP)
        (H0 : s = generateS grp (List.length cand_all))
        (H1 : cpi = generatePermutationCommitment grp (List.length cand_all) pi s)
        (H2 : shuffledcp = shuffle grp (List.length cand_all) cp pi r)
        (H3 : zkprowshuffle = shuffle_zkp grp (List.length cand_all)
                                          cp shuffledcp pi cpi s r),
        verify_shuffle grp (List.length cand_all)
                       cp shuffledcp cpi zkprowshuffle = true. 
    

  
    (* Shuffle introduce reencryption *)
    Axiom shuffle_perm :
      forall grp n f pi r g, 
        shuffle grp (n : nat) (f : cand -> ciphertext) (pi : Permutation) r = g ->
        forall c, decrypt_message grp privatekey (g c) =
             decrypt_message grp privatekey (compose f (projT1 pi) c).

    (* end of axioms about shuffle. *)     
                                                         
    
  
    (* Decidability of pair of cand *)
    Lemma pair_cand_dec : forall (c d : cand * cand), {c = d} + {c <> d}.
    Proof.
      intros c d. destruct c, d.
      pose proof (dec_cand c c1).
      pose proof (dec_cand c0 c2).
      destruct H, H0. left.
      subst. reflexivity.
      right. unfold not. intros. inversion H. pose proof (n H2). inversion H0.
      right. unfold not. intros. inversion H. pose proof (n H1). inversion H0.
      right. unfold not. intros. inversion H. pose proof (n H1). inversion H0.
    Qed.

          

    Lemma every_cand_t : forall (c d : cand), In (c, d) (all_pairs cand_all).
    Proof.
      intros c d. apply  all_pairsin; auto.
    Qed.

    Lemma non_empty_cand_pair : all_pairs cand_all <> [].
    Proof.
      destruct cand_all. pose proof (cand_not_nil eq_refl). inversion H.
      simpl. intro. inversion H.
    Qed.
    
    
    (* A ballot is in matrix with all the entries are
       -1, 0 and 1 with no cyles *)
    Definition matrix_ballot_valid (p : pballot) :=
      (forall c d : cand, In (p c d) [-1; 0; 1]) /\
      valid cand p. 

   
    Lemma partition_integer : forall (b : Z),
        ({b = -1} + {b = 0} + {b = 1}) + {b <> -1 /\ b <> 0 /\ b <> 1}.
    Proof.
      intros b.
      destruct (Z_le_dec b (-2)). right.  omega.
      destruct (Z_ge_dec b 2). right. omega.
      left. assert (b > -2) by omega.
      assert (b < 2) by omega.  clear n. clear n0.
      destruct (Z_eq_dec b (-1)). left. left. auto.
      destruct (Z_eq_dec b 0). left. right.  auto.
      assert (b = 1) by omega. right.  auto.
    Qed.
    
   
    (* I learned pretty nice trick *)
    Lemma finite_gen : forall (b : cand -> cand -> Z) (l : list (cand * cand)),
        (forall c d,  In (c, d) l -> {b c d = -1} + {b c d = 0} + {b c d = 1}) +
        (exists c d,  In (c, d) l /\ b c d <> -1 /\ b c d <> 0 /\ b c d <> 1).
    Proof.
      intros b l.
      induction l. 
      + left; intros. inversion H.
      + destruct IHl. 
        destruct a as (c1, c2).
        destruct (partition_integer (b c1 c2)); swap 1 2.  
        right.  exists c1, c2. split. cbn. left. auto. auto.
        left. intros. 
        destruct (pair_cand_dec (c, d) (c1, c2)). 
        inversion e.  subst. auto.
        assert (In (c, d) l).
        destruct H. unfold not in n. symmetry in H. pose proof (n H).
        inversion H0. assumption.
        pose proof (s _ _ H0). auto.
        right.  destruct e as [c [d Hin]].
        exists c, d. destruct Hin. split. cbn.  right. auto.
        auto.
    Qed.
   

    Lemma  finiteness : forall  (b : cand -> cand -> Z)
                           (l : list (cand * cand))  (H : forall c d, In (c, d) l),
        (forall c d, {b c d = -1} + {b c d = 0} + {b c d = 1}) +
        (exists c d,  b c d <> -1 /\ b c d <> 0 /\ b c d <> 1).
    Proof.
      intros.
      pose proof (finite_gen b l).
      destruct X. left.  intros. apply s. auto.
      right. destruct e as [c [d Hin]].
      exists c, d. destruct Hin. assumption.
    Qed.   

    Lemma dec_pballot :
      forall (p : pballot), 
        {forall c d : cand, In (p c d) [-1; 0; 1]} +
        {~(forall c d : cand, In (p c d) [-1; 0; 1])}.
    Proof.
      intros.
      pose proof (finiteness p (all_pairs cand_all) every_cand_t).
      destruct X. left. intros.
      destruct (s c d) as [[H1 | H1] | H1].
      left. auto.  right; left. auto. right; right. simpl. auto.
      right. intro. destruct e as [c [d [Hp1 [Hp2 Hp3]]]].
      pose proof (H c d). destruct H0. congruence.
      destruct H0. congruence. destruct H0. congruence. inversion H0.
    Qed.
    
    
    Lemma pballot_valid_dec :
      forall b : pballot, {valid cand b} +
                     {~(valid cand b)}.
     Proof.
       intros b. pose proof (decidable_valid cand b dec_cand).
       pose proof (finiteness b (all_pairs cand_all) every_cand_t) as Ht.
       destruct Ht. pose proof (X s).
       unfold finite in X0. apply X0. exists cand_all. auto.
       right.  unfold valid, not; intros. destruct H as [f Hf].
       destruct e as [c [d [He1 [He2 He3]]]]. pose proof (Hf c d).
       destruct H. destruct H0.
       destruct (lt_eq_lt_dec (f c) (f d)) as [[H2 | H2] | H2].
       apply H in H2. congruence. apply H0 in H2. congruence.
       assert (f c > f d)%nat by omega. apply H1 in H3. congruence.
     Qed.

          
    (* The decrypted ballot is either valid or not valid *)
    Lemma matrix_ballot_valid_dec :
        forall p : pballot, {matrix_ballot_valid p} +
                            {~matrix_ballot_valid p}.
    Proof.
      intros p. 
      destruct (dec_pballot p); destruct (pballot_valid_dec p).
      left. unfold matrix_ballot_valid. intuition.
      right. unfold matrix_ballot_valid. unfold not. intros.
      destruct H. pose proof (n H0). auto.
      right. unfold not. intros; intuition. destruct H.
      pose proof (n H). auto.
      right. unfold not. intros. destruct H.
      pose proof (n H). auto.
    Defined.

   
   (* Returns true if v is row permutation of u by pi *)
    Definition verify_row_permutation_ballot grp
               (u : eballot) (v : eballot)
               (cpi : Commitment) (zkppermuv : cand -> ZKP) : cand -> bool := 
      fun c => verify_shuffle grp (List.length cand_all)
                           (u c) (v c) cpi (zkppermuv c). 
      
    (* cth column of w is permutation of cth column of v by pi *)                  
    Definition verify_col_permutation_ballot (grp : Group)
               (v : eballot) (w : eballot)
               (cpi : Commitment) (zkppermvw  : cand -> ZKP) : cand ->  bool :=
      fun c => verify_shuffle grp (List.length cand_all)
                           (fun d => v d c) (fun d => w d c) cpi (zkppermvw c).


    
    Inductive EState : Type :=
    | epartial : (list eballot * list eballot) ->
                 (cand -> cand -> ciphertext) -> EState
    | edecrypt : (cand -> cand -> plaintext) -> EState
    | ewinners : (cand -> bool) -> EState.
  
    
    Inductive ECount (grp : Group) (bs : list eballot) : EState -> Type :=
    | ecax (us : list eballot) (encm : cand -> cand -> ciphertext)
           (decm : cand -> cand -> plaintext)
           (zkpdec : cand -> cand -> string) :
        us = bs ->
        (forall c d : cand, decm c d = 0) -> 
        (forall c d, verify_zero_knowledge_decryption_proof 
                  grp (decm c d) (encm c d) (zkpdec c d) = true) ->
        ECount grp bs (epartial (us, []) encm)
    | ecvalid (u : eballot) (v : eballot) (w : eballot)
              (b : pballot) (zkppermuv : cand -> ZKP)
              (zkppermvw : cand -> ZKP) (zkpdecw : cand -> cand -> string)
              (cpi : Commitment) (zkpcpi : ZKP)
              (us : list eballot) (m nm : cand -> cand -> ciphertext)
              (inbs : list eballot) :
        ECount grp bs (epartial (u :: us, inbs) m) ->
        matrix_ballot_valid b ->
        (* commitment proof *)
        verify_permutation_commitment grp (List.length cand_all) cpi zkpcpi = true ->
        (forall c, verify_row_permutation_ballot grp u v cpi zkppermuv c = true)  ->
        (forall c, verify_col_permutation_ballot grp v w cpi zkppermvw c = true)  ->
        (forall c d, verify_zero_knowledge_decryption_proof 
                  grp (b c d) (w c d) (zkpdecw c d) = true) (* b is honest decryption of w *) ->
        (forall c d, nm c d = homomorphic_addition grp (u c d) (m c d)) -> 
        ECount grp bs (epartial (us, inbs) nm)
    | ecinvalid (u : eballot) (v : eballot) (w : eballot)
              (b : pballot) (zkppermuv : cand -> ZKP)
              (zkppermvw : cand -> ZKP) (zkpdecw : cand -> cand -> string)
              (cpi : Commitment) (zkpcpi : ZKP)
              (us : list eballot) (m : cand -> cand -> ciphertext)
              (inbs : list eballot) :
        ECount grp bs (epartial (u :: us, inbs) m) ->
        ~matrix_ballot_valid b ->
        (* commitment proof *)
        verify_permutation_commitment grp (List.length cand_all) cpi zkpcpi = true  ->
        (forall c, verify_row_permutation_ballot grp u v cpi zkppermuv c = true) ->
        (forall c, verify_col_permutation_ballot grp v w cpi zkppermvw c = true) ->
        (forall c d, verify_zero_knowledge_decryption_proof 
                  grp (b c d) (w c d) (zkpdecw c d) = true) (* b is honest decryption of w *) ->
        ECount grp bs (epartial (us, (u :: inbs)) m)
    | ecdecrypt inbs (encm : cand -> cand -> ciphertext)
                (decm : cand -> cand -> plaintext)
                (zkp : cand -> cand -> string) :
        ECount grp bs (epartial ([], inbs) encm) ->
        (forall c d, verify_zero_knowledge_decryption_proof
                  grp (decm c d) (encm c d) (zkp c d) = true) ->
        ECount grp bs (edecrypt decm)
    | ecfin dm w (d : (forall c, (wins_type dm c) + (loses_type dm c))) :
        ECount grp bs (edecrypt dm) ->
        (forall c, w c = true <-> (exists x, d c = inl x)) ->
        (forall c, w c = false <-> (exists x, d c = inr x)) ->
        ECount grp bs (ewinners w).  
    
        
   
    
    Lemma ecount_all_ballot :
      forall (grp : Group) (bs : list eballot), existsT encm, ECount grp bs (epartial (bs, []) encm).
    Proof.
      intros.
      remember (encrypt_message grp 0) as encm. exists (fun c d => encm).
      pose proof (ecax grp bs bs (fun c d => encm)
                       (fun c d => 0)
                       (fun c d => construct_zero_knowledge_decryption_proof
                                  grp privatekey encm)
                       eq_refl (fun c d => eq_refl)).
      assert (forall c d : cand,
                 verify_zero_knowledge_decryption_proof
                   grp ((fun _ _ : cand => 0) c d)
                   ((fun _ _ : cand => encm) c d)
                   ((fun _ _ : cand =>
                       construct_zero_knowledge_decryption_proof grp privatekey encm) c d) =
                 true).
      intros. apply verify_true.
      symmetry. rewrite Heqencm. apply decryption_deterministic.
      pose proof (X H). auto.
    Qed.


    (* A helper function which convertes list to function. It helpful in using list as a 
       function *)
    Lemma idx_search_list : forall (A : Type) (c : cand) (cl : list cand)
                              (l : list A) (Hin : In c cl)
                              (H : List.length l = List.length cl), A.
    Proof.
      intros A c.
      refine (fix F cl :=
                match cl as cl'
                      return (forall l, In c cl' ->
                                   Datatypes.length l = Datatypes.length cl' -> A) with
                | [] => fun l Hin Heq => match Hin with end
                | c0 :: cs => fun l => match l with
                                  | [] => fun Hin Heq => _
                                  | a :: t => fun Hin Heq =>
                                               match dec_cand c c0 with
                                               | left _ => a
                                               | right _ => _
                                               end
                                  end
                                              
                end); inversion Heq.
      assert (Ht : In c cs).
      destruct Hin; try congruence.
      refine (F cs t Ht H0).
    Defined.
    
                                                     

    (* This Lemma states that we will always end up in state where 
       we have counted all the ballots by taking one ballot, and deciding if it's 
       valid or not. If valid then add it to encrypted marging otherwise add it invalid  
       ballot list *)
    Lemma ppartial_count_all_counted grp bs : forall ts inbs m,
        ECount grp bs (epartial (ts, inbs) m) -> existsT i nm, (ECount grp bs (epartial ([], i) nm)).
    Proof.    
      induction ts as [|u ts IHs].
      intros inbs m He.
      exists inbs, m. auto.
      intros inbs m He. 
      (* The idea is u valid or not valid which can be shown via u -> (* row permutation *) -> v
        -> (* colume permutation *) -> w -> (* decryption *) -> b *)
      (* generate permutation pi to permute ballot*) 
      remember (generatePermutation grp (List.length cand_all)) as pi.
      (* generate randomness S *)
      remember (generateS grp (List.length cand_all)) as s.
      (* commit to this permutation  using randomness s*)
      remember (generatePermutationCommitment grp (List.length cand_all) pi s) as cpi.
      (* generate zero knowledge proof of commitment *)
      remember (zkpPermutationCommitment grp (List.length cand_all)
                                         pi cpi s) as zkpcpi.
      (* At this point I can assert that 
         verify_permutation_commitment grp (List.length cand_all) cpi zkpcpi = true 
         using the Axiom permutation_commitment_axiom *)
      assert (verify_permutation_commitment grp (List.length cand_all) cpi zkpcpi = true).
      pose proof (permutation_commitment_axiom
                    grp pi cpi s zkpcpi Heqs Heqcpi Heqzkpcpi). auto.
      
      (* Convert u -> rowpermute pi -> v *)
      (* Generate randomness to use in shuffle *)
      remember (map (fun _ => generateR grp (List.length cand_all)) cand_all) as rrowlistvalues.
      (* I have generated the randomness for each row and use them in shuffling. 
         It would be good idea to convert rlistvalues to rfunvalues by 
         using search_list function *)
      assert (Datatypes.length rrowlistvalues = Datatypes.length cand_all).
      rewrite Heqrrowlistvalues. rewrite map_length; auto. 
      remember (fun c => idx_search_list _ c cand_all rrowlistvalues (cand_fin c) H0) as rrowfunvalues.
      (* Now I have converted rrowlistvalues in rrowfunvalues. Smile *)

      (* get the ballot v by shuffling each row by pi and randomness R *)
      remember (fun c =>
                  shuffle grp (List.length cand_all)
                          (u c) pi (rrowfunvalues c)) as v.
      (* construct zero knowledge proof of shuffle that v is row shuffle of u by pi
         using the same randomness R which used in shuffle *)
      remember (fun c =>
                  shuffle_zkp grp (List.length cand_all)
                              (u c) (v c) pi cpi s (rrowfunvalues c)) as zkppermuv.
      
           
      (* Show that verify_row_permutation_ballot u v cpi zkppermuv return true.
         The property here is construct matrix from u and v and comp
         This is bit tricky so I am leaving it for the moment because we need to 
         massage the axioms *)
      assert (Ht1 : forall c, verify_row_permutation_ballot grp u v cpi zkppermuv c = true). 
      intros; unfold verify_row_permutation_ballot.
      pose proof (verify_shuffle_axiom grp pi cpi s (u c) (v c) (rrowfunvalues c) (zkppermuv c)
                                       Heqs Heqcpi).
      assert (Hvr : v c = shuffle grp (Datatypes.length cand_all)
                                               (u c) pi (rrowfunvalues c)).
      rewrite Heqv; try auto.
      specialize (H1 Hvr). clear Hvr. rewrite Heqzkppermuv in H1.
      specialize (H1 eq_refl). rewrite Heqzkppermuv; try auto. 

      (* generate again the randomness R to make cryptography great again *)
      remember (map (fun _ => generateR grp (List.length cand_all)) cand_all) as rcollistvalues.
      (* I have generated the randomness for each column and use them in shuffling. 
         It would be good idea to convert rcollistvalues to rcolfunvalues by 
         using search_list function *)
      assert (Datatypes.length rcollistvalues = Datatypes.length cand_all).
      rewrite Heqrcollistvalues. rewrite map_length; auto. 
      remember (fun c => idx_search_list _ c cand_all rcollistvalues (cand_fin c) H1)
        as rcolfunvalues.
      
      (* convert v -> column permutation pi -> w *)
      (* get the colum shuffled ballot. Notice that t is now in column form. For any candidate c, 
         it fetches the cth column of v and permute them by pi, so t c is 
         permuted cth column of v. Important *)
      remember (fun c =>
                  shuffle grp (List.length cand_all)
                          (fun d => v d c) pi (rcolfunvalues c)) as t. 
      remember (fun c d => t d c) as w. (* transpose t to get w in row form *)
        
      (* construct zero knowledge proof of shuffle that w is column permutation of v by pi *)
      remember (fun c =>
                  shuffle_zkp grp (List.length cand_all)
                              (fun d => v d c) (fun d => w d c) pi cpi s (rcolfunvalues c))
        as zkppermvw.
      
      assert (Ht2 : forall c, verify_col_permutation_ballot grp v w cpi zkppermvw c = true).
      intros. unfold verify_col_permutation_ballot. 
      pose proof (verify_shuffle_axiom grp pi cpi s (fun d => v d c) (fun d => w d c)
                                       (rcolfunvalues c) (zkppermvw c) Heqs Heqcpi).
      rewrite Heqw in H2.
      assert ((fun d => t c d) = shuffle grp (Datatypes.length cand_all)
                                      (fun d : cand => v d c) pi (rcolfunvalues c)).
      rewrite Heqt; try auto.
      specialize (H2 H3).
      rewrite Heqzkppermvw in H2. rewrite Heqw in H2. specialize (H2 eq_refl).
      rewrite Heqzkppermvw; rewrite Heqw. try auto. 

      
      (* Now decrypt the ballot w. *)
      remember (fun c d => decrypt_message grp privatekey (w c d)) as b.
      (* construct zero knowledge proof of decryption *)
      remember (fun c d => construct_zero_knowledge_decryption_proof
                          grp privatekey (w c d)) as zkpdecw.
      (* Show that the zkpdecw is true b is honest decryption of w *)
      assert (Ht3 : forall c d, verify_zero_knowledge_decryption_proof
                              grp (b c d) (w c d) (zkpdecw c d) = true).
      intros c d. rewrite Heqzkpdecw.
      apply verify_true. rewrite Heqb. reflexivity.

      (* Now connect the validity of b to validity of u. A valid b means 
         there is no cycle in b which reflects back to ballot u and 
         u is homomorphically added to margin. 
         If b is not valid then it contains cycle and this reflects back to u *)
      destruct (matrix_ballot_valid_dec b) as [Hb | Hnb].
      (* Since b is valid so add the ballot u to margin m and call it nm *)
      remember (fun c d => homomorphic_addition grp (u c d) (m c d)) as nm.
      assert (Ht4 : forall c d, nm c d = homomorphic_addition grp (u c d) (m c d)).
      intros c d.  rewrite Heqnm. reflexivity.
      
      (* ecvalid *) 
      pose proof (ecvalid grp bs u v w b zkppermuv zkppermvw
                          zkpdecw cpi zkpcpi ts m nm inbs He
                          Hb H Ht1 Ht2 Ht3 Ht4).
      (* Induction Hypothesis *)
      destruct (IHs _ _ X) as [inb [mrg T]].
      exists inb, mrg. assumption.
 
      (* ecinvalid *)
      pose proof (ecinvalid grp bs u v w b zkppermuv zkppermvw
                            zkpdecw cpi zkpcpi ts m inbs He Hnb H
                            Ht1 Ht2 Ht3).
      destruct (IHs (u :: inbs) m X) as [inb [mrg T]].
      exists inb, mrg. assumption.
    Qed.
    
      



     (* for every list of incoming ballots, we can progress the count to a state where all
     ballots are processed *)
    Lemma  pall_ballots_counted (grp : Group) (bs : list eballot) :
      existsT i m, ECount grp bs (epartial ([], i) m).
    Proof.
      pose proof (ecount_all_ballot grp bs) as Hs.
      destruct Hs as [encm Heg].
      pose proof (ppartial_count_all_counted grp bs bs [] encm Heg).
      destruct X as [i [nm He]]. exists i, nm. assumption.
    Defined.
    

      
    (* We decrypt the encrypted margin to run the computation *)
    Lemma decrypt_margin (grp : Group) (bs : list eballot) :
      existsT m, ECount grp bs (edecrypt m).
    Proof.
      remember (pall_ballots_counted grp bs) as Hc.
      destruct Hc as [i [m Hcount]].
      remember (fun c d => decrypt_message grp privatekey (m c d)) as decm.
      remember (fun c d => construct_zero_knowledge_decryption_proof
                          grp privatekey (m c d)) as zkpdecm. 
      exists decm.
      apply ecdecrypt with (inbs := i) (encm := m) (zkp := zkpdecm). 
      assumption.
      intros c d. rewrite Heqzkpdecm.
      apply verify_true.
      rewrite Heqdecm. reflexivity.
    Defined. 

    (* The main theorem: for every list of ballots, we can find a boolean function that decides
     winners, together with evidences of the correctness of this determination *)
    Lemma pschulze_winners (grp : Group) (bs : list eballot) :
      existsT (f : cand -> bool), ECount grp bs (ewinners f).
    Proof.
      destruct (decrypt_margin grp bs) as [dm Hecount].
      exists (c_wins dm).
      pose proof (ecfin grp bs dm (c_wins dm) (wins_loses_type_dec dm) Hecount).
      pose proof (X (c_wins_true_type dm) (c_wins_false_type dm)).
      auto.
    Defined.

    (* Everthing below is connecting the plain text winner to ciphertext winner
       and ciphertext winner to plaintext winner *)

    (* Now Try to prove that result computed by schulze_winner 
       pschulze_winners are same if ballots match *)
    
    (* This function connects ballot ot pballot *)
    Definition map_ballot_pballot (b : ballot) (p : pballot) :=
      ((exists c,  b c = 0)%nat /\ ~matrix_ballot_valid p) \/
      (matrix_ballot_valid p /\ (forall c, b c > 0)%nat /\
       (forall c d, (p c d = 1 <-> (b c < b d)%nat) /\
               (p c d = 0 <-> (b c = b d)%nat) /\
               (p c d = -1 <-> (b c > b d)%nat))).
    
    
    (* This reason I am going with this proof is that my proofs depends on this. 
       But inductive type is more elegant *)
    Fixpoint mapping_ballot_pballot (bs : list ballot) (pbs : list pballot) : Prop. 
    Proof.
      refine (match bs, pbs with
              | [], [] => True
              | [], h :: _ => False 
              | h :: _, [] => False
              | h1 :: t1, h2 :: t2 =>
                map_ballot_pballot h1 h2 /\
                 mapping_ballot_pballot t1 t2
              end); inversion H.
    Defined.

    Lemma connect_validity_of_ballot_pballot :
      forall (b : ballot) (p : pballot),
        map_ballot_pballot b p -> 
        proj1_sig (bool_of_sumbool (ballot_valid_dec b)) = true <->
        proj1_sig (bool_of_sumbool (matrix_ballot_valid_dec p)) = true.
    Proof.
      intros b p H.
      split; intros.
      unfold map_ballot_pballot in H. destruct H.
      destruct H.  destruct H as [c H].
      destruct (bool_of_sumbool (ballot_valid_dec b)).
      simpl in H0. rewrite H0 in y.  pose proof (y c).  omega.
      destruct H as [H1 [H2 H3]].
      destruct (bool_of_sumbool (matrix_ballot_valid_dec p)).
      simpl in *. destruct x. auto. congruence.

      unfold map_ballot_pballot in H.
      destruct H.  destruct H as [c H].
      destruct (bool_of_sumbool (matrix_ballot_valid_dec p)). simpl in *.
      rewrite H0 in y. congruence.
      destruct H as [H1 [H2 H3]].
      destruct (bool_of_sumbool (ballot_valid_dec b)). simpl in *.
      destruct x.  auto. destruct y. pose proof (H2 x). omega.
    Qed.

    Lemma connect_invalidity_of_ballot_pballot :
      forall (b : ballot) (p : pballot),
        map_ballot_pballot b p -> 
        proj1_sig (bool_of_sumbool (ballot_valid_dec b)) = false <->
        proj1_sig (bool_of_sumbool (matrix_ballot_valid_dec p)) = false.
    Proof.
      intros b p H.
      split; intros.
      unfold map_ballot_pballot in H.
      destruct H. destruct H.  destruct H as [c H].
      destruct (bool_of_sumbool (matrix_ballot_valid_dec p)).
      simpl in *. destruct x; congruence.
      destruct H. destruct H1.
      destruct (bool_of_sumbool (ballot_valid_dec b)). simpl in *.
      rewrite H0 in y. destruct y.  pose proof (H1 x0). omega.

      unfold map_ballot_pballot in H.
      destruct H. destruct H. destruct H as [c H].
      destruct (bool_of_sumbool (ballot_valid_dec b)). simpl in *.
      destruct x. pose proof (y c). omega. auto.
      destruct H. destruct H1.
      destruct (bool_of_sumbool (matrix_ballot_valid_dec p)).
      simpl in *. rewrite H0 in y. congruence.
    Qed.
 
    
   
    Require Import Coq.Logic.FunctionalExtensionality.
    Lemma margin_same_from_both_existential 
          (grp : Group) (bs : list ballot) (ebs : list eballot) (pbs : list pballot)
          (Ht : pbs = map (fun x => (fun c d => decrypt_message grp privatekey (x c d))) ebs)
          (H1 : mapping_ballot_pballot bs pbs) :
      forall (s : State),
        Count bs s ->
        forall (ts : list ballot) (tinbs : list ballot)
          (m : cand -> cand -> Z), (* valid ballot, invalid ballot, running margin *)
          s = partial (ts, tinbs) m ->
          existsT 
            (ets : list eballot) (etinbs : list eballot)
            (tpbs : list pballot) (etpbs : list pballot)
            (em : cand -> cand -> ciphertext),
      (ECount grp ebs (epartial (ets, etinbs) em) *
       (m = fun c d => decrypt_message grp privatekey (em c d)) *
       (tpbs =  map (fun x => (fun c d => decrypt_message grp privatekey (x c d))) ets) *
       (etpbs =  map (fun x => (fun c d => decrypt_message grp privatekey (x c d))) etinbs) * 
       mapping_ballot_pballot ts tpbs *
       mapping_ballot_pballot tinbs etpbs)%type.
    Proof.   
      intros s H.  
      (* induction on structure of H *)
      induction H. intros. inversion H.
      remember (fun c d => encrypt_message grp (m c d)) as em.
      exists ebs, [], pbs, [], em.
      pose proof (ecax grp ebs ebs em m
                       (fun c d => construct_zero_knowledge_decryption_proof
                                  grp privatekey (em c d)) eq_refl e0).
      simpl in X.
      assert (forall c d : cand,
                 verify_zero_knowledge_decryption_proof
                   grp (m c d) (em c d)
                   (construct_zero_knowledge_decryption_proof grp privatekey (em c d)) = true).
      intros. subst. apply verify_true. rewrite decryption_deterministic. auto.
      specialize (X H0). clear H0.
      repeat split. assumption.
      rewrite Heqem.
      apply functional_extensionality. intros.
      apply functional_extensionality. intros.
      rewrite decryption_deterministic. rewrite H4. auto.
      assumption. rewrite H2 in e. rewrite <- e in H1.
      assumption. 
      (* first case finished *)  
 
      (*  Count bs (partial (u :: us, inbs) m) and u is valid 
           g : forall c : cand, u c > 0 *)
      intros.  inversion H0.  
      specialize (IHCount (u :: us) inbs m eq_refl). 
      destruct IHCount as [ets [etinbs [tbps [etpbs [em H6]]]]].
      destruct H6. destruct p. destruct p. destruct p. destruct p.
      (* From m2 we can infer that tbps <> [] and it can be written as 
         tbps = t :: tpbs'. From this statement we can infer that ets <> [] using e0.
         ets = e :: ets'. 
         u is valid => t valid => it's encryption e is also valid 
         go for ecvalid case *)

      assert (forall (A : Type) (l : list A),
                 l <> [] -> existsT t l', l = t :: l').
      intros. destruct l.  intuition. exists a0, l. auto.
      assert (tbps <> []). unfold not. intros. destruct tbps.
      simpl in m2. inversion m2. inversion H2. 
      destruct (X _ _ H2) as [t [tbps' Htpbs']]. clear H2.
      rewrite Htpbs' in e0.
      assert (ets <> []). unfold not. intros.
      destruct ets. simpl in e0. inversion e0. inversion H2.
      destruct (X _ _ H2) as [en [ets' Hets']]. clear H2.
      rewrite Hets' in e0. inversion e0. clear e0. clear X.
      rewrite Htpbs' in m2. simpl in m2. destruct m2.
      rewrite Hets' in e1. 
      (*  ECount grp ebs (epartial (en :: ets', etinbs) em) 
          and u is valid then t is valid and it's encryption is valid *)
      pose proof (ecvalid grp ebs).
      (* u = en, v = row permutation of u, w is column permutation of v *)
      (* generate permutation *)  
      remember (generatePermutation grp (List.length cand_all)) as pi.
      (* generate randomness S *)
      remember  (generateS grp (List.length cand_all)) as s.
      (* commit it *)
      remember (generatePermutationCommitment grp (List.length cand_all) pi s) as cpi.
      (* generate zero knowledge proof of commitment *)
      remember (zkpPermutationCommitment grp (List.length cand_all)
                                         pi cpi s) as zkpcpi. 
      (* At this point I can assert that 
         verify_permutation_commitment grp (List.length cand_all) cpi zkpcpi = true 
         using the Axiom permutation_commitment_axiom *)
      assert (verify_permutation_commitment grp (List.length cand_all) cpi zkpcpi = true).
      pose proof (permutation_commitment_axiom
                    grp pi cpi s zkpcpi Heqs Heqcpi Heqzkpcpi). auto.



      (* Convert en -> rowpermute pi -> v *)
      (* What if i separate the R from shuffle ? *)
      (* This is what I am doing *)
      remember (map (fun _ => generateR grp (List.length cand_all)) cand_all) as rrowlistvalues.
      (* I have generated the randomness for each row and use them in shuffling. 
         It would be good idea to convert rlistvalues to rfunvalues by 
         using search_list function *)
      assert (Datatypes.length rrowlistvalues = Datatypes.length cand_all).
      rewrite Heqrrowlistvalues. rewrite map_length; auto. 
      remember (fun c => idx_search_list _ c cand_all rrowlistvalues (cand_fin c) H10) as rrowfunvalues.
      (* Now I have converted rrowlistvalues in rrowfunvalues. Smile *)
      
      (* Create a axiom, generateRandomR which takes grp and returns R. Use this R 
         in Shuffle *)
      (* get the ballot v by shuffling each row by pi and randomness R *)
      remember (fun c =>
                  shuffle grp (List.length cand_all)
                          (en c) pi (rrowfunvalues c)) as v.
      (* construct zero knowledge proof of shuffle that v is row shuffle of u by pi
         using the same randomness R which used in shuffle *)
      remember (fun c =>
                  shuffle_zkp grp (List.length cand_all)
                              (en c) (v c) pi cpi s (rrowfunvalues c)) as zkppermuv.
      
      
      (* Show that verify_row_permutation_ballot u v cpi zkppermuv return true.
         The property here is construct matrix from u and v and comp
         This is bit tricky so I am leaving it for the moment because we need to 
         massage the axioms *)
      assert (Ht1 : forall c, verify_row_permutation_ballot grp en v cpi zkppermuv c = true). 
      intros; unfold verify_row_permutation_ballot.
      pose proof (verify_shuffle_axiom grp pi cpi s (en c) (v c) (rrowfunvalues c) (zkppermuv c)
                                       Heqs Heqcpi).
      assert (Hvr : v c = shuffle grp (Datatypes.length cand_all)
                                               (en c) pi (rrowfunvalues c)).
      rewrite Heqv; try auto.
      specialize (H11 Hvr). clear Hvr. rewrite Heqzkppermuv in H11.
      specialize (H11 eq_refl). rewrite Heqzkppermuv; try auto. 

      

       (* generate again the randomness R to make sure that cryptographic sprit is high *)
      remember (map (fun _ => generateR grp (List.length cand_all)) cand_all) as rcollistvalues.
      (* I have generated the randomness for each column and use them in shuffling. 
         It would be good idea to convert rcollistvalues to rcolfunvalues by 
         using search_list function *)
      assert (Datatypes.length rcollistvalues = Datatypes.length cand_all).
      rewrite Heqrcollistvalues. rewrite map_length; auto. 
      remember (fun c => idx_search_list _ c cand_all rcollistvalues (cand_fin c) H11)
        as rcolfunvalues.
     
       
      (* convert v -> column permutation pi -> w *)
      (* get the colum shuffled ballot. Notice that t is now in column form. For any candidate c, 
         it fetches the cth column of v and permute them by pi, so t c is 
         permuted cth column of v. Important *)
      remember (fun c =>
                  shuffle grp (List.length cand_all)
                          (fun d => v d c) pi (rcolfunvalues c)) as tt. 
      remember (fun c d => tt d c) as w. (* transpose t to get w in row form *)
        
      (* construct zero knowledge proof of shuffle that w is column permutation of v by pi *)
      remember (fun c =>
                  shuffle_zkp grp (List.length cand_all)
                              (fun d => v d c) (fun d => w d c) pi cpi s (rcolfunvalues c))
        as zkppermvw.
      
      assert (Ht2 : forall c, verify_col_permutation_ballot grp v w cpi zkppermvw c = true).
      intros. unfold verify_col_permutation_ballot. 
      pose proof (verify_shuffle_axiom grp pi cpi s (fun d => v d c) (fun d => w d c)
                                       (rcolfunvalues c) (zkppermvw c) Heqs Heqcpi).
      rewrite Heqw in H12.
      assert ((fun d => tt c d) = shuffle grp (Datatypes.length cand_all)
                                      (fun d : cand => v d c) pi (rcolfunvalues c)).
      rewrite Heqtt; try auto.
      specialize (H12 H13).
      rewrite Heqzkppermvw in H12. rewrite Heqw in H12. specialize (H12 eq_refl).
      rewrite Heqzkppermvw; rewrite Heqw. try auto. 


      
      (* Now decrypt the ballot w *)
      remember (fun c d => decrypt_message grp privatekey (w c d)) as b.
      (* construct zero knowledge proof of decryption *)
      remember (fun c d => construct_zero_knowledge_decryption_proof
                          grp privatekey (w c d)) as zkpdecw.
      (* Show that the zkpdecw is true b is honest decryption of w *)
      assert (Ht3 : forall c d, verify_zero_knowledge_decryption_proof
                              grp (b c d) (w c d) (zkpdecw c d) = true).
      intros c d. rewrite Heqzkpdecw.
      apply verify_true. rewrite Heqb. reflexivity.
      
      (* At this point we need Axioms which connects the validity of en to b 
         g : forall c : cand, u c > 0 
         H2 : map_ballot_pballot u t
         H6 : t = (fun c d : cand => decrypt_message grp privatekey (en c d)) 
         u is valid and it infers that t is also valid. 
         t is valid then it's encryption en is also valid *)
      pose proof (proj1 (connect_validity_of_ballot_pballot u t H2)). 
      (* I know that u is valid (Hypothesis g) *)
      assert (proj1_sig (bool_of_sumbool (matrix_ballot_valid_dec t)) = true).
      destruct (ballot_valid_dec u). simpl in H12. 
      specialize (H12 eq_refl). auto.
      destruct e0. pose proof (g x). omega.
      clear H12. destruct (matrix_ballot_valid_dec t); swap 1 2.
      inversion H13. clear H13.   
      (* Now I have m2 : matrix_ballot_valid t => en should be valid 
         and row and column permutation *)     
      assert (matrix_ballot_valid b).
      unfold matrix_ballot_valid in *. unfold valid in *.
     
       
      destruct pi as [pi Sig].
      
      (* Each row of v is shuffle of each row of en by permutation pi *)
      
      assert (forall c d, t c d = decrypt_message grp privatekey (en c d)).
      intros. rewrite H6. auto.

      (* Interpretation of permutation. v c d = en c (pi d) and it means 
         that element at '(pi d)' position in cth row of en goes to 'd' position of cth row in v *) 
      assert (forall c d, decrypt_message grp privatekey (v c d) =
                     decrypt_message grp privatekey (en c (pi d))). 
      rewrite Heqv. intros. 
      assert (shuffle grp (Datatypes.length cand_all) (en c)
                      (existT (fun pi : cand -> cand => Bijective pi) pi Sig) (rrowfunvalues c) = v c).
      rewrite Heqv. auto.
      rewrite H13. eapply shuffle_perm in H13. 
      unfold compose in H13.
      instantiate (1 := d) in H13. simpl in H13. assumption.

      assert (forall c d, decrypt_message grp privatekey (w c d) =
                     decrypt_message grp privatekey (v (pi c) d)).  
      rewrite Heqw. intros. rewrite Heqtt.
      assert (shuffle grp (Datatypes.length cand_all) (fun d0 : cand => v d0 d)
                      (existT (fun pi0 : cand -> cand => Bijective pi0) pi Sig) (rcolfunvalues d) =
              fun d0 => w d0 d).
      rewrite Heqw. rewrite Heqtt. auto.
      rewrite H14. eapply shuffle_perm in H14.
      unfold compose in H14.
      instantiate (1 := c) in H14. cbn in H14. auto.

      assert (forall c d, decrypt_message grp privatekey (w c d) =
                     decrypt_message grp privatekey (en (pi c) (pi d))).
      intros. rewrite  H14. rewrite H13. auto.
     

       
      assert (forall c d, b c d = t (pi c) (pi d)).
      intros. rewrite Heqb. rewrite H15. auto.
      destruct m2 as [Tin [gfun Hg]]. split. intros.
      rewrite H16. auto. 
      
      exists (fun c => gfun (pi c)); intros. rewrite H16. 
      eapply Hg. 
      
      (* I am the happiest person on earth *)
      
        
      specialize (X en v w b zkppermuv zkppermvw zkpdecw cpi
                    zkpcpi ets' em
                    (fun c d : cand => homomorphic_addition
                                      grp (en c d) (em c d))
                    etinbs e1 H12 H9 Ht1 Ht2 Ht3).
      simpl in X.
      assert ((forall c d : cand,
                  homomorphic_addition grp (en c d) (em c d) =
                  homomorphic_addition grp (en c d) (em c d))).
      auto.
      specialize (X H13).
      (*  ECount grp ebs
        (epartial (ets', etinbs) (fun c d : cand => homomorphic_addition grp (en c d) (em c d))) *)
      exists ets', etinbs, tbps', etpbs, (fun c d : cand => homomorphic_addition grp (en c d) (em c d)).
      repeat split. auto. 
      apply functional_extensionality. intros.
      apply functional_extensionality. intros.
      pose proof (homomorphic_addition_axiom grp (en x x0) (em x x0)).
      rewrite H14.
      (*  m = (fun c d : cand => decrypt_message grp privatekey (em c d))
           H6 : t = (fun c d : cand => decrypt_message grp privatekey (en c d)) *)
      assert (t x x0 = decrypt_message grp privatekey (en x x0)).
      rewrite H6. auto.
      assert (m x x0 = decrypt_message grp privatekey (em x x0)).
      rewrite e2. auto.
      rewrite <- H15. rewrite <- H16.
      rewrite <- H5.
      destruct (a x x0) as [H17 [H18 H19]].
      unfold matrix_ballot_valid in m2. destruct m2. 
      unfold map_ballot_pballot in H2. 
      destruct H2.  destruct H2. destruct H2 as [c H2].
      specialize (g c). omega.
      (*  H2 : matrix_ballot_valid t /\
       (forall c : cand, (u c > 0)%nat) /\
       (forall c d : cand,
        (t c d = 1 <-> (u c < u d)%nat) /\
        (t c d = 0 <-> u c = u d) /\ (t c d = -1 <-> (u c > u d)%nat)) *)
      destruct H2 as [H2m [H2c H2cd]].
      destruct (H2cd x x0) as [H2cdt1 [H2cdt2 H2cdt3]].
      destruct (lt_eq_lt_dec (u x) (u x0)) as [[Hul | Hul] | Hul].
      pose proof (H17 Hul).
      apply H2cdt1 in Hul. rewrite Hul. omega.
      pose proof (H18 Hul). apply H2cdt2 in Hul. rewrite Hul. omega.
      assert (u x > u x0)%nat by omega.
      pose proof (H19 H2). apply H2cdt3 in H2. rewrite H2.  omega.
      assumption. assumption. rewrite H3 in H8. assumption.
      rewrite H4 in m1. assumption.
      (* Wohoo. Valid case discharged. *)

      (* Now we are in situation where u is not valid. *)
      intros. inversion H0.
      assert (proj1_sig (bool_of_sumbool (ballot_valid_dec u)) = false).
      destruct (ballot_valid_dec u); simpl; try auto.
      destruct e as [c Hc]. pose proof (g c). omega.

      assert (forall (A : Type) (l : list A),
                 l <> [] -> existsT t l', l = t :: l').
      intros. destruct l.  intuition.
      exists a, l. auto.
      assert (tinbs <> []). unfold not; intros.
      destruct tinbs.  inversion H4. inversion H6.
      destruct (X _ tinbs H6) as [t [tinbs' Hinbs']].
      clear H6.
      (* u :: inbs = t :: tinbs' *)
      rewrite Hinbs' in H4.  inversion H4.
      specialize (IHCount (u :: us) tinbs' m). rewrite H8 in IHCount.
      specialize (IHCount eq_refl).
      destruct IHCount as [ets [etinbs [tpbs [etpbs [em Htt]]]]].
      destruct Htt as [Htt Hte]. destruct Htt as [Htt Hp].
      destruct Htt as [Htt Het].
      destruct Htt as [Htt Htp].
      destruct Htt as [He Hm].

      assert (tpbs <> []). unfold not. intros. destruct tpbs.
      simpl in Hp. inversion Hp. inversion H6.
      destruct (X _ _ H6) as [tp [tpbs' Htpbs']].
      rewrite Htpbs' in Htp.
      assert (ets <> []). unfold not. intros.
      rewrite H9 in Htp. inversion Htp.
      destruct (X _ _ H9) as [en [ets' Hets']]. clear H6; clear H9.
      rewrite Hets' in He. rewrite Htpbs' in Hp. simpl in Hp.
      destruct Hp. rewrite Hets' in Htp. inversion Htp.

      (* ecinvalid *)

      (* generate permutation *)  
      remember (generatePermutation grp (List.length cand_all)) as pi.
      (* generate randomness S *)
      remember (generateS grp (List.length cand_all)) as s.
      (* commit it *)
      remember (generatePermutationCommitment grp (List.length cand_all) pi s) as cpi.
      (* generate zero knowledge proof of commitment *)
      remember (zkpPermutationCommitment grp (List.length cand_all)
                                         pi cpi s) as zkpcpi. 
      (* At this point I can assert that 
         verify_permutation_commitment grp (List.length cand_all) cpi zkpcpi = true 
         using the Axiom permutation_commitment_axiom *)
      assert (verify_permutation_commitment grp (List.length cand_all) cpi zkpcpi = true).
      pose proof (permutation_commitment_axiom
                    grp pi cpi s zkpcpi  Heqs Heqcpi Heqzkpcpi). auto.

      
      (* Convert en -> rowpermute pi -> v *)
      (* What if i separate the R from shuffle ? *)
      (* This is what I am doing *)
      remember (map (fun _ => generateR grp (List.length cand_all)) cand_all) as rrowlistvalues.
      (* I have generated the randomness for each row and use them in shuffling. 
         It would be good idea to convert rlistvalues to rfunvalues by 
         using search_list function *)
      assert (Datatypes.length rrowlistvalues = Datatypes.length cand_all).
      rewrite Heqrrowlistvalues. rewrite map_length; auto.
      remember (fun c => idx_search_list _ c cand_all rrowlistvalues (cand_fin c) H13) as rrowfunvalues.
      (* Now I have converted rrowlistvalues in rrowfunvalues. Smile *)
      
      (* Create a axiom, generateRandomR which takes grp and returns R. Use this R 
         in Shuffle *)
      (* get the ballot v by shuffling each row by pi and randomness R *)
      remember (fun c =>
                  shuffle grp (List.length cand_all)
                          (en c) pi (rrowfunvalues c)) as v.
      (* construct zero knowledge proof of shuffle that v is row shuffle of u by pi
         using the same randomness R which used in shuffle *)
      remember (fun c =>
                  shuffle_zkp grp (List.length cand_all)
                              (en c) (v c) pi cpi s (rrowfunvalues c)) as zkppermuv.
      
           
      (* Show that verify_row_permutation_ballot u v cpi zkppermuv return true.
         The property here is construct matrix from u and v and comp
         This is bit tricky so I am leaving it for the moment because we need to 
         massage the axioms *)
      assert (Ht1 : forall c, verify_row_permutation_ballot grp en v cpi zkppermuv c = true). 
      intros; unfold verify_row_permutation_ballot.
      pose proof (verify_shuffle_axiom grp pi cpi s (en c) (v c) (rrowfunvalues c) (zkppermuv c)
                                       Heqs Heqcpi).
      assert (Hvr : v c = shuffle grp (Datatypes.length cand_all)
                                               (en c) pi (rrowfunvalues c)).
      rewrite Heqv; try auto.
      specialize (H14 Hvr). clear Hvr. rewrite Heqzkppermuv in H14.
      specialize (H14 eq_refl). rewrite Heqzkppermuv; try auto. 



       (* generate again the randomness R to make sure that cryptographic sprit is high *)
      remember (map (fun _ => generateR grp (List.length cand_all)) cand_all) as rcollistvalues.
      (* I have generated the randomness for each column and use them in shuffling. 
         It would be good idea to convert rcollistvalues to rcolfunvalues by 
         using search_list function *)
      assert (Datatypes.length rcollistvalues = Datatypes.length cand_all).
      rewrite Heqrcollistvalues. rewrite map_length; auto. 
      remember (fun c => idx_search_list _ c cand_all rcollistvalues (cand_fin c) H14)
        as rcolfunvalues.
     
       
      (* convert v -> column permutation pi -> w *)
      (* get the colum shuffled ballot. Notice that t is now in column form. For any candidate c, 
         it fetches the cth column of v and permute them by pi, so t c is 
         permuted cth column of v. Important *)
      remember (fun c =>
                  shuffle grp (List.length cand_all)
                          (fun d => v d c) pi (rcolfunvalues c)) as tt. 
      remember (fun c d => tt d c) as w. (* transpose t to get w in row form *)
        
      (* construct zero knowledge proof of shuffle that w is column permutation of v by pi *)
      remember (fun c =>
                  shuffle_zkp grp (List.length cand_all)
                              (fun d => v d c) (fun d => w d c) pi cpi s (rcolfunvalues c))
        as zkppermvw.
      
      assert (Ht2 : forall c, verify_col_permutation_ballot grp v w cpi zkppermvw c = true).
      intros. unfold verify_col_permutation_ballot. 
      pose proof (verify_shuffle_axiom grp pi cpi s (fun d => v d c) (fun d => w d c)
                                       (rcolfunvalues c) (zkppermvw c) Heqs Heqcpi).
      rewrite Heqw in H15.
      assert ((fun d => tt c d) = shuffle grp (Datatypes.length cand_all)
                                      (fun d : cand => v d c) pi (rcolfunvalues c)).
      rewrite Heqtt; try auto.
      specialize (H15 H16).
      rewrite Heqzkppermvw in H15. rewrite Heqw in H15. specialize (H15 eq_refl).
      rewrite Heqzkppermvw; rewrite Heqw. try auto. 

      
      (* Now decrypt the ballot w *)
      remember (fun c d => decrypt_message grp privatekey (w c d)) as b.
      (* construct zero knowledge proof of decryption *)
      remember (fun c d => construct_zero_knowledge_decryption_proof
                          grp privatekey (w c d)) as zkpdecw.
      (* Show that the zkpdecw is true b is honest decryption of w *)
      assert (Ht3 : forall c d, verify_zero_knowledge_decryption_proof
                              grp (b c d) (w c d) (zkpdecw c d) = true).
      intros c d. rewrite Heqzkpdecw.
      apply verify_true. rewrite Heqb. reflexivity. 
      (* At this point we need Axioms which connects the validity of en to b 
         e : exists c : cand, u c = 0 
         H6 : map_ballot_pballot u tp
         H11 : tp = (fun c d : cand => decrypt_message grp privatekey (en c d))
         u is invalid and it infers that t is also invalid. 
         t is invalid then it's encryption en is also invalid *)
      assert (proj1_sig (bool_of_sumbool (ballot_valid_dec u)) = false).
      destruct (bool_of_sumbool (ballot_valid_dec u)). simpl.
      destruct x. destruct e as [e Hc]. pose proof (y e). omega.
      auto.
      pose proof (proj1 (connect_invalidity_of_ballot_pballot u tp H6) H15).
      (* I know that u is valid (Hypothesis g) *)
      assert (~matrix_ballot_valid tp).
      destruct (matrix_ballot_valid_dec tp). simpl in H16.
      inversion H16. auto. 
  
      (* tp is decryption of en. tp is invalid so as en. and every permutation of 
         en => v => w => b *)
      assert (~matrix_ballot_valid b).
      unfold not in *.  intros m2. destruct H17.
      unfold matrix_ballot_valid in *. unfold valid in *.
      
      destruct pi as [pi Sig]. 
      (* Each row of v is shuffle of each row of en by permutation pi *)
      
      assert (forall c d, tp c d = decrypt_message grp privatekey (en c d)).
      intros. rewrite H11. auto.


      assert (forall c d, decrypt_message grp privatekey (v c d) =
                     decrypt_message grp privatekey (en c (pi d))). 
      rewrite Heqv. intros. 
      assert (shuffle grp (Datatypes.length cand_all) (en c)
                      (existT (fun pi : cand -> cand => Bijective pi) pi Sig) (rrowfunvalues c) = v c).
      rewrite Heqv. auto.
      rewrite H18. eapply shuffle_perm in H18. 
      unfold compose in H18.
      instantiate (1 := d) in H18. simpl in H18. assumption.

      assert (forall c d, decrypt_message grp privatekey (w c d) =
                     decrypt_message grp privatekey (v (pi c) d)).   
      rewrite Heqw. intros. rewrite Heqtt.
      assert (shuffle grp (Datatypes.length cand_all) (fun d0 : cand => v d0 d)
                      (existT (fun pi0 : cand -> cand => Bijective pi0) pi Sig) (rcolfunvalues d) =
              fun d0 => w d0 d).
      rewrite Heqw. rewrite Heqtt. auto.
      rewrite H19. eapply shuffle_perm in H19.
      unfold compose in H19.
      instantiate (1 := c) in H19. cbn in H19. auto.

      assert (forall c d, decrypt_message grp privatekey (w c d) =
                     decrypt_message grp privatekey (en (pi c) (pi d))).
      intros. rewrite  H19. rewrite H18. auto.

      
      assert (forall c d, b c d = tp (pi c) (pi d)).
      intros. rewrite Heqb. rewrite H20. auto. 
      assert (Hsig : Bijective pi). auto.
      unfold Bijective in Hsig.
      destruct Hsig as [pi_inv [Hg1 Hg2]].
      
      destruct m2 as [Tin [gfun Hg]]. split. intros.     
      pose proof (Tin (pi_inv c) (pi_inv d)).
      pose proof (H21 (pi_inv c) (pi_inv d)).
      rewrite Hg2 in H23. rewrite Hg2 in H23.
      rewrite H23 in H22. auto.
      (* existence of function *)
      exists (fun c => gfun (pi_inv c)); intros.
      pose proof (Hg (pi_inv c) (pi_inv d)).
      rewrite H21 in H22.  rewrite Hg2 in H22.
      rewrite Hg2 in H22. auto.
            
      pose proof (ecinvalid grp ebs en v w b zkppermuv zkppermvw zkpdecw cpi
                            zkpcpi  ets' em etinbs He H18 H10 Ht1 Ht2 Ht3).
      exists ets', (en :: etinbs), tpbs', (tp :: etpbs), em.
      repeat split. assumption. rewrite <- H5. assumption.
      assumption. simpl. rewrite H11.  apply f_equal. assumption.
      rewrite H3 in H9.  assumption. rewrite <- H7. assumption.
      assumption.
      (* Invalid case finished *)
      intros. inversion H0.
    Qed.   
    
    
    Fixpoint compute_margin (bs : list ballot) :=
      match bs with
      | [] => fun c d => 0
      | h :: t =>
        match ballot_valid_dec h with
        | left _ => update_marg h (compute_margin t)
        | right _ => compute_margin t
        end
      end.

    Lemma nat_dec_me n m : 
        ({n < m} + {m < n} + {n = m})%nat.
    Proof. 
      induction n in m |- *; destruct m; auto with arith.
      destruct (IHn m) as [H|H]; auto with arith.
      destruct H; auto with arith.
    Qed.
    
    Lemma compute_assoc :
      forall u a m, (forall c, u c > 0)%nat -> (forall c, a c > 0)%nat ->  
               update_marg u (update_marg a m) = update_marg a (update_marg u m).
    Proof.
      intros.  unfold update_marg.
      apply functional_extensionality; intros.
      apply functional_extensionality; intros.
      destruct (nat_dec_me (u x) (u x0)) as [[H1 | H1] | H1].
      apply Nat.ltb_lt in H1. rewrite H1.
      destruct (nat_dec_me (a x) (a x0)) as [[H2 | H2] | H2].
      apply Nat.ltb_lt in H2.  rewrite H2.  auto.
      assert (Ht : (a x <? a x0)%nat = false).
      apply Nat.ltb_nlt. unfold not. intros. omega.
      rewrite Ht.  apply Nat.ltb_lt in H2. rewrite H2.  omega.
      rewrite H2. rewrite Nat.ltb_irrefl. auto.
      assert (Ht : (u x <? u x0)%nat = false).
      apply Nat.ltb_nlt. unfold not. intros. omega.
      rewrite Ht.  apply Nat.ltb_lt in H1. rewrite H1.
      destruct (nat_dec_me (a x) (a x0)) as [[H2 | H2] | H2].
      apply Nat.ltb_lt in H2.  rewrite H2. omega.
      assert (Htt : (a x <? a x0)%nat = false).
      apply Nat.ltb_nlt. unfold not. intros. omega.
      rewrite Htt.  apply Nat.ltb_lt in H2. rewrite H2.  omega.
      rewrite H2. rewrite Nat.ltb_irrefl. omega.
      (* u x = u x0 *)
      rewrite H1. rewrite Nat.ltb_irrefl.
      destruct (nat_dec_me (a x) (a x0)) as [[H2 | H2] | H2].
      apply Nat.ltb_lt in H2.  rewrite H2. omega.
      assert (Htt : (a x <? a x0)%nat = false).
      apply Nat.ltb_nlt. unfold not. intros. omega.
      rewrite Htt.  apply Nat.ltb_lt in H2. rewrite H2.  omega.
      rewrite H2. rewrite Nat.ltb_irrefl. omega.
    Qed.
     
      
      
    
    Lemma valid_compute_margin_distributes :
      forall bs (u : ballot), (forall c, u c > 0)%nat ->
                         compute_margin (bs ++ [u]) = update_marg u (compute_margin bs).
    Proof.
      induction bs; simpl; intros; try auto.
      destruct (ballot_valid_dec u). auto.
      destruct e as [e He]. pose proof (H e). omega.
       
      destruct (ballot_valid_dec a).
      rewrite (compute_assoc _ _ _ H g).
      specialize (IHbs u H). rewrite IHbs. auto.
      pose proof (IHbs u H). assumption.
    Qed. 
    

    Lemma invalid_compute_margin_same :
      forall bs (u : ballot), (exists c, u c = 0)%nat -> compute_margin (bs ++ [u]) = compute_margin bs.
    Proof.
      induction bs; simpl; intros; try auto.
      destruct (ballot_valid_dec u). destruct H as [e H].
      pose proof (g e). omega. auto.
      
      destruct (ballot_valid_dec a).
      pose proof (IHbs u H). rewrite H0. auto.
      pose proof (IHbs u H). auto.
    Qed.
      

    Lemma tail_count : forall bs s,
        Count bs s ->
        forall us inbs m,
          s = partial (us, inbs) m ->
          exists cs', bs = cs' ++ us  /\ m = compute_margin cs'.
    Proof.
      (* This proof is for m = compute_margin cs' *)
      intros bs s Hc.
      induction Hc; simpl; intros; inversion H; subst; clear H.
      exists []. split. auto.  simpl.
      apply functional_extensionality; intros.
      apply functional_extensionality; intros.
      auto.
      
      pose proof (IHHc (u :: us0) inbs0 m eq_refl).
      destruct H as [cs' [H1 H2]].
      exists (cs' ++ [u]). split. rewrite app_assoc_reverse. auto.
      rewrite (valid_compute_margin_distributes _ _ g). rewrite <- H2. 
      unfold update_marg. apply functional_extensionality; intros.
      apply functional_extensionality; intros. 
      destruct (a x x0) as [H3 [H4 H5]].
      destruct (lt_eq_lt_dec (u x) (u x0)) as [[H6 | H6] | H6].
      pose proof (H3 H6).
      apply Nat.ltb_lt in H6.  rewrite H6. assumption.
      rewrite H6.
      rewrite Nat.ltb_irrefl. apply H4. assumption.
      assert ((u x <? u x0) = false)%nat. apply Nat.ltb_nlt.
      unfold not.  intros. omega.
      rewrite H. clear H.  SearchAbout (_ <? _)%nat.
      assert (u x > u x0)%nat by omega. 
      apply Nat.ltb_lt in H6. rewrite H6.  
      apply H5. assumption.
      
      pose proof (IHHc (u :: us0) inbs m0 eq_refl).
      destruct H as [cs' [H1 H2]].
      exists (cs' ++ [u]). split. rewrite app_assoc_reverse. auto.
      rewrite (invalid_compute_margin_same _ _ e). auto.  
    Qed.
    


    (* Counting same list of ballots would give same margin *)
    Lemma unique_margin : forall bs inbs inbs0 m m0 s s0 (c0 : Count bs s) (c1 : Count bs s0),
        s = partial ([], inbs) m ->
        s0 = partial ([], inbs0) m0 -> m = m0.
    Proof.
      intros.
      pose proof (tail_count bs s c0 [] inbs m H).
      destruct H1 as [cs' [H1 H2]]. rewrite <- app_nil_end in H1.
      rewrite <- H1 in H2.
      pose proof (tail_count bs s0 c1 [] inbs0 m0 H0).
      destruct H3 as [cs1' [H1' H2']]. rewrite <- app_nil_end in H1'.
      rewrite <- H1' in H2'. rewrite H2, H2'. reflexivity.
    Qed.
    
   
                                                                            
    (* Uniqueness of winners *)
    Lemma uniqueness_proof : forall bs w w',
        Count bs (winners w) -> Count bs (winners w') -> w = w'.
    Proof.
      intros bs w w' H1 H2.     
      inversion H1. inversion H2.
      subst.  pose proof (unique_margin bs inbs inbs0 m m0 _ _  X X0 eq_refl eq_refl).
      subst.  apply functional_extensionality; intros.
      specialize (H3 x). specialize (H0 x). 
      specialize (H5 x). specialize (H6 x). 
      remember (w x) as Hw.
      remember (w' x) as Hw'.
      destruct Hw; destruct Hw'; try auto. 
      specialize ((proj1 H6) eq_refl); intros.
      specialize ((proj1 H0) eq_refl); intros.
      destruct H. destruct H4.
      destruct H3. destruct H5.
      pose proof (loses_type_prop m0 x x0).
      pose proof (loses_prop_iterated_marg m0 x H9).
      destruct H10 as [dd H10].
      pose proof (wins_type_prop m0 x x1).
      pose proof (wins_prop_iterated_marg m0 x H11).
      pose proof (H12 dd). omega.

      specialize ((proj1 H3) eq_refl); intros.
      specialize ((proj1 H5) eq_refl); intros.
      destruct H. destruct H4.
      destruct H3. destruct H5.
      pose proof (loses_type_prop m0 x x0).
      pose proof (loses_prop_iterated_marg m0 x H9).
      destruct H10 as [dd H10].
      pose proof (wins_type_prop m0 x x1).
      pose proof (wins_prop_iterated_marg m0 x H11).
      pose proof (H12 dd). omega.
    Qed.
    
     

    (* If there one to one correspondence between ballots and encrypted ballots, 
       then computing winners via plaintext ballot is same as encrypted ballot *)
    Lemma final_correctness :
    forall  (grp : Group) (bs : list ballot) (pbs : list pballot) (ebs : list eballot)
      (w : cand -> bool)
      (H : pbs = map (fun x => (fun c d => decrypt_message grp privatekey (x c d))) ebs)
      (H2 : mapping_ballot_pballot bs pbs), (* valid b <-> valid pb *)
      Count bs (winners w) -> ECount grp ebs (ewinners w).
    Proof.
      (* Show that margin computed from bs is same as ebs *)
      intros grp bs pbs ebs w H0 H1 H2.
      destruct (all_ballots_counted bs) as [inb [fm Hm]].
      pose proof (margin_same_from_both_existential grp bs ebs pbs H0 H1 _ Hm
                                                    [] inb fm eq_refl).
      destruct X as [ets [etinbs [tpbs [etpbs [em He]]]]].
      destruct He as [[[[[He Hfm] Htpb] Hetp] Het] Hie].
      assert(tpbs = []). destruct tpbs. auto. simpl in Het. inversion Het.
      assert (ets = []). destruct ets. auto.
      rewrite H in Htpb. inversion Htpb. rewrite H3 in He. 

      pose proof (ecdecrypt grp ebs etinbs
                            em
                            fm
                            (fun c d => construct_zero_knowledge_decryption_proof
                                       grp privatekey (em c d)) He).
      simpl in X. 
      assert (forall c d : cand,
                 verify_zero_knowledge_decryption_proof
                   grp (fm c d) (em c d)
                   (construct_zero_knowledge_decryption_proof grp privatekey (em c d)) = true).
      intros. apply verify_true. rewrite Hfm. auto.
      specialize (X H4). clear H4.

      pose proof (fin bs fm inb (c_wins fm) (wins_loses_type_dec fm) Hm
                      (c_wins_true_type fm) (c_wins_false_type fm)).
      pose proof (ecfin grp ebs fm (c_wins fm) (wins_loses_type_dec fm)
                        X (c_wins_true_type fm) (c_wins_false_type fm)).
      
      (* All I need now is assert c_wins fm = w *)
      pose proof (uniqueness_proof bs w (c_wins fm) H2 X0).
      rewrite H4. assumption.
    Qed.

    (* This axiom states that 
       if verify_zero_knowledge_decryption_proof grp d c zkp = true then 
       d is honest decryption of c *)
    Axiom decryption_from_zkp_proof :
      forall grp c d zkp, 
        verify_zero_knowledge_decryption_proof grp d c zkp = true -> 
        d = decrypt_message grp privatekey c.

    (* Permutation Axiom *)
    Axiom perm_axiom :
      forall grp cpi zkpcpi, 
        verify_permutation_commitment grp (Datatypes.length cand_all) cpi zkpcpi = true ->
        existsT (pi : Permutation), forall (f g : cand -> ciphertext) (zkppf : ZKP), 
      verify_shuffle grp (Datatypes.length cand_all) f g cpi zkppf = true ->
          forall c, decrypt_message grp privatekey (g c) =
               decrypt_message grp privatekey (compose f (projT1 pi) c).
    
    (* existence of permutation pi which is used to permute the ballots 
       v, and w *)
    Theorem existence_of_perm :
      forall grp cpi zkpcpi,
        verify_permutation_commitment grp (Datatypes.length cand_all) cpi zkpcpi = true ->
        existsT (pi : Permutation),  forall u v w zkppermuv zkppermvw, 
      (forall c, verify_row_permutation_ballot grp u v cpi zkppermuv c = true) ->
      (forall c, verify_col_permutation_ballot grp v w cpi zkppermvw c = true) ->
      forall c d, (decrypt_message grp privatekey (v c d) =
            decrypt_message grp privatekey (u c (projT1 pi d))) /\
           (decrypt_message grp privatekey (w c d) =
            decrypt_message grp privatekey (v (projT1 pi c) d)).
    Proof.
      intros. pose proof (perm_axiom grp cpi zkpcpi H).  
      destruct X as [pi X]. 
      exists pi. intros.
      unfold verify_row_permutation_ballot in H0.
      unfold verify_col_permutation_ballot in H1.
      split. pose proof (X (u c) (v c) (zkppermuv c) (H0 c)). apply H2.   
      pose proof (X (fun c0 => v c0 d) (fun c0 => w c0 d) (zkppermvw d) (H1 d)).
      apply H2.
    Qed.
    
   
      
   
    
    
    
    
    (* Correctness in reverse direction. From encrypted ballots to plaintext *)
    Lemma margin_same_from_both_existential_rev 
          (grp : Group) (bs : list ballot) (ebs : list eballot) (pbs : list pballot)
          (Ht : pbs = map (fun x => (fun c d => decrypt_message grp privatekey (x c d))) ebs)
          (H1 : mapping_ballot_pballot bs pbs) :
      forall (s : EState),
        ECount grp ebs s ->
        forall (ets etinbs : list eballot)
          (tpbs etpbs : list pballot)
          (em : cand -> cand -> ciphertext)
          (H2 : tpbs = map (fun x => (fun c d => decrypt_message grp privatekey (x c d))) ets)
          (H3 : etpbs = map (fun x => (fun c d => decrypt_message grp privatekey (x c d))) etinbs),
          s = epartial (ets, etinbs) em ->
          existsT
            (ts tinbs : list ballot)
            (m : cand -> cand -> Z), 
      (Count bs (partial (ts, tinbs) m) *
       (m = fun c d => decrypt_message grp privatekey (em c d)) *
       mapping_ballot_pballot ts tpbs *
       mapping_ballot_pballot tinbs etpbs)%type.
    Proof.
      intros s H.
      induction H; intros. inversion H. 
      exists bs, [], decm.
      pose proof (ax bs bs decm eq_refl e0).
      repeat split.  auto.
      (* Now from e1, I need to infer that decm is honest decryption of em *)
      apply functional_extensionality; intros.
      apply functional_extensionality; intros.
      pose proof (e1 x x0). subst. 
      (* This goal should be discharged from assumption H0 using the following Axiom.
         verify_zero_knowledge_decryption_proof grp dec enc zkp = true -> 
         dec = decryption_message grp privatekey enc *)
      apply  decryption_from_zkp_proof with
          (grp := grp) (c := em x x0) (zkp := zkpdec x x0); auto.
      
      subst. assumption.
      rewrite <- H5 in H3.  simpl in H3.  rewrite H3. apply I.
      
      (* ECvalid case. matrix_ballot valid b. 
         I am going to add u in encrypted margin *)
      inversion H0.
      specialize (IHECount (u :: us) inbs). simpl in IHECount.
      specialize (IHECount ((fun c d : cand => decrypt_message grp privatekey (u c d)) :: tpbs)
                           etpbs m).
      rewrite H2 in IHECount. rewrite H5 in IHECount.
      specialize (IHECount eq_refl).
      rewrite <- H6 in H3.
      specialize (IHECount H3 eq_refl).
      destruct IHECount as [ts [tinbs [decm IHm]]].
      destruct IHm as [[[IHc Hdec] Hts] Hm].
      destruct ts.  inversion Hts.  simpl in Hts.
      destruct Hts. 
      (*  m0 : matrix_ballot_valid b
          e : verify_permutation_commitment grp (Datatypes.length cand_all) cpi zkpcpi = true
          e0 : forall c : cand, verify_row_permutation_ballot grp u v cpi zkppermuv c = true
          e1 : forall c : cand, verify_col_permutation_ballot grp v w cpi zkppermvw c = true
          e2 : forall c d : cand,
                 verify_zero_knowledge_decryption_proof grp (b c d) (w c d) (zkpdecw c d) = true
         I know b is valid so this translates back to validity of u. 
         Since u is valid then b0 is valid *)
      assert (matrix_ballot_valid
                (fun c d : cand => decrypt_message grp privatekey (u c d))).
      pose proof (existence_of_perm grp cpi zkpcpi e). 
      destruct X as [[pi Hsig] Hf].
      specialize (Hf u v w zkppermuv zkppermvw e0 e1).
      destruct m0 as [Min [fn Mas]].

     assert (forall c d, decrypt_message grp privatekey (v c d) =
                     decrypt_message grp privatekey (u c (pi d))). 
     intros. pose proof (Hf c d).
     simpl in H9. destruct H9. assumption.

     assert (forall c d, decrypt_message grp privatekey (w c d) =
                    decrypt_message grp privatekey (v (pi c) d)). 
     intros. pose proof (Hf c d). destruct H10. assumption.

     assert (forall c d, decrypt_message grp privatekey (w c d) =
                    decrypt_message grp privatekey (u (pi c) (pi d))).
     intros. rewrite H10. rewrite H9. auto.

     assert (forall c d, b c d = decrypt_message grp privatekey (w c d)).
     intros. pose proof (decryption_from_zkp_proof grp (w c d) (b c d) (zkpdecw c d) (e2 c d));
               assumption.

     assert (forall c d, b c d = decrypt_message grp privatekey (u (pi c) (pi d))).
     intros.  rewrite H12. auto.
 
     split. intros. unfold Bijective in Hsig.
     destruct Hsig as [pi_inv [Hp1 Hp2]].
     pose proof (H13 (pi_inv c) (pi_inv d)). rewrite Hp2 in H14. rewrite Hp2 in H14.
     rewrite <- H14. auto.
     unfold valid.  destruct Hsig as [pi_inv [Hp1 Hp2]].
     exists (fun c => fn (pi_inv c)). intros. 
     pose proof (H13 (pi_inv c) (pi_inv d)).
     rewrite Hp2 in H14. rewrite Hp2 in H14.  rewrite <- H14.
     pose proof (Mas (pi_inv c) (pi_inv d)). assumption.
     
     

     
     pose proof (proj2 (connect_validity_of_ballot_pballot
                           b0
                           (fun c d : cand => decrypt_message grp privatekey (u c d)) H4)).
      assert ( forall c : cand, (b0 c > 0)%nat).
      destruct ((matrix_ballot_valid_dec (fun c d : cand => decrypt_message grp privatekey (u c d)))).
      simpl in H10. specialize (H10 eq_refl).
      destruct (ballot_valid_dec b0). auto. inversion H10. congruence.
      (* Add this ballot in count *)
      pose proof (cvalid bs b0 ts decm
                         (fun c d : cand => decrypt_message grp privatekey (nm c d))
                         tinbs IHc H11).
      unfold map_ballot_pballot in H4.      
      assert (
          forall c d : cand,
            ((b0 c < b0 d)%nat ->
             (fun c0 d0 : cand => decrypt_message grp privatekey (nm c0 d0)) c d = decm c d + 1) /\
            (b0 c = b0 d -> (fun c0 d0 : cand => decrypt_message grp privatekey (nm c0 d0)) c d
                           = decm c d) /\
            ((b0 c > b0 d)%nat ->
             (fun c0 d0 : cand => decrypt_message grp privatekey (nm c0 d0)) c d = decm c d - 1)).
      destruct H4.  destruct H4.  congruence.
      destruct H4. destruct H12.  
      intros.
      split. intros. 
      pose proof (H13 c d).  rewrite e3.
      rewrite homomorphic_addition_axiom. destruct H15. apply H15 in H14.
      rewrite H14.  rewrite Hdec.
      rewrite Z.add_1_l. auto.
      split. intros. 
      destruct (H13 c d) as [Htt [H15 H16]].
      apply H15 in H14.  rewrite e3. rewrite homomorphic_addition_axiom.
      rewrite H14.  simpl. rewrite Hdec. auto.
      intros. destruct (H13 c d) as [Htt [H15 H16]].
      apply H16 in H14.  rewrite e3. rewrite homomorphic_addition_axiom.
      rewrite H14.  rewrite Hdec. rewrite Z.add_comm. auto.
      specialize (X H12).
      exists ts, tinbs, (fun c d : cand => decrypt_message grp privatekey (nm c d)).
      split. split. split. auto. rewrite H7. auto.  rewrite <- H2 in H8. auto.
      auto.
      (* Finished cvalid case *)

      inversion H0.
      assert (etinbs <> []). destruct etinbs. inversion H6.
      unfold not. intro. inversion H4.
      destruct etinbs.  unfold not in H4.
      pose proof (H4 eq_refl). inversion H8.
      inversion H6. 
      specialize (IHECount (u :: us) etinbs).
      simpl in IHECount.
      specialize (IHECount ((fun c d : cand => decrypt_message grp privatekey (u c d)) :: tpbs)).
      simpl in H3. destruct etpbs. inversion H3.
      inversion H3.
      specialize (IHECount etpbs m). rewrite <- H5 in H2.
      rewrite H2 in IHECount. specialize (IHECount eq_refl H12).
      rewrite H10 in IHECount. specialize (IHECount eq_refl).
      destruct IHECount as [ts [tinbs [decm IHm]]].
      destruct IHm as [[[IHc Hdec] Hts] Hm].
      destruct ts. inversion Hts. destruct Hts.
      (* 
       n : ~ matrix_ballot_valid b
       e : verify_permutation_commitment grp (Datatypes.length cand_all) cpi zkpcpi = true
       e0 : forall c : cand, verify_row_permutation_ballot grp u v cpi zkppermuv c = true
       e1 : forall c : cand, verify_col_permutation_ballot grp v w cpi zkppermvw c = true
       e2 : forall c d : cand,
          verify_zero_knowledge_decryption_proof grp (b c d) (w c d) (zkpdecw c d) = true
       I know b is invalid so this translates back to invalidity of u. 
         Since u is invalid then b0 is invalid *)
      assert (~matrix_ballot_valid
               (fun c d : cand => decrypt_message grp privatekey (u c d))).
      intro. apply n.
      
      unfold matrix_ballot_valid in *.  destruct H14 as [H14 [g Hg]].
      
      pose proof (existence_of_perm grp cpi zkpcpi e). 
      destruct X as [[pi Hsig] Hf].
      specialize (Hf u v w zkppermuv zkppermvw e0 e1).
      
      assert (forall c d, decrypt_message grp privatekey (v c d) =
                     decrypt_message grp privatekey (u c (pi d))). 
      intros. pose proof (Hf c d).
      simpl in H15. destruct H15. assumption.
      
      assert (forall c d, decrypt_message grp privatekey (w c d) =
                     decrypt_message grp privatekey (v (pi c) d)). 
      intros. pose proof (Hf c d). simpl in H16. destruct H16. assumption.
      
      assert (forall c d, decrypt_message grp privatekey (w c d) =
                     decrypt_message grp privatekey (u (pi c) (pi d))).
      intros. rewrite H16. rewrite H15. auto.
      
      assert (forall c d, b c d = decrypt_message grp privatekey (w c d)).
      intros. pose proof (decryption_from_zkp_proof grp (w c d) (b c d) (zkpdecw c d) (e2 c d));
                assumption.
      
      assert (forall c d, b c d = decrypt_message grp privatekey (u (pi c) (pi d))).
      intros.  rewrite H18. auto.
      
      
     
      split. intros. unfold Bijective in Hsig.
      destruct Hsig as [pi_inv [Hp1 Hp2]].
      rewrite H19. auto. 
      unfold valid.  destruct Hsig as [pi_inv [Hp1 Hp2]].
      exists (fun c => g (pi c)). intros.
      rewrite H19. auto. 
      
      pose proof (proj2 (connect_invalidity_of_ballot_pballot
                           b0
                           (fun c d : cand => decrypt_message grp privatekey (u c d)) H8)).
      assert (exists c, (b0 c = 0)%nat). 
      destruct (matrix_ballot_valid_dec (fun c d : cand => decrypt_message grp privatekey (u c d))).
      congruence. simpl in H15. specialize (H15 eq_refl).
      destruct (ballot_valid_dec b0). inversion H15.  auto.
      pose proof (cinvalid bs b0 ts decm tinbs IHc H16).
      exists ts, (b0 :: tinbs), decm.
      split. split. split. auto.
      rewrite H7 in Hdec. auto.
      rewrite <- H2 in H13. auto.
      simpl.  split. rewrite <- H9. auto.
      rewrite <- H12. auto.
      (* finished cinvalid *)
      inversion H0.
      inversion H0.  
    Qed.


    


    (* This function computes the encrypted margin *)
    Fixpoint compute_margin_enc grp (bs : list eballot) :=
      match bs with
      | [] => fun c d => encrypt_message grp 0
      | h :: t =>
        match matrix_ballot_valid_dec (fun c d => decrypt_message grp privatekey (h c d)) with
        | left _ => fun c d => homomorphic_addition grp (h c d) (compute_margin_enc grp t c d)
        | right _ => compute_margin_enc grp t
        end
      end.

    Require Import Psatz.
      
      
    Lemma valid_compute_margin_distributes_enc :
      forall grp bs (u : eballot),
        matrix_ballot_valid (fun c d : cand => decrypt_message grp privatekey (u c d)) ->
        forall c d, decrypt_message grp privatekey
                               (compute_margin_enc grp (bs ++ [u]) c d) =
               decrypt_message grp privatekey
                               (homomorphic_addition grp (u c d) (compute_margin_enc grp bs c d)).
    Proof.
      induction bs.
      + simpl; intros. 
        destruct (matrix_ballot_valid_dec (fun c d : cand => decrypt_message grp privatekey (u c d)));
          try congruence.
      + intros. simpl.
        destruct (matrix_ballot_valid_dec (fun c d : cand => decrypt_message grp privatekey (a c d))).
        pose proof (IHbs _ H).
        repeat rewrite homomorphic_addition_axiom. rewrite H0.
        rewrite homomorphic_addition_axiom. lia. auto. 
    Qed.
    
        


    Lemma invalid_compute_margin_same_enc :
      forall grp bs (u : eballot),
        ~matrix_ballot_valid (fun c d : cand => decrypt_message grp privatekey (u c d)) ->
        forall c d, decrypt_message grp privatekey 
                               (compute_margin_enc grp (bs ++ [u]) c d) = 
               decrypt_message grp privatekey (compute_margin_enc grp bs c d).
    Proof.
      induction bs; simpl; intros; try auto.
      destruct (matrix_ballot_valid_dec _).
      congruence. auto.
      
      destruct (matrix_ballot_valid_dec _).
      pose proof (IHbs u H).
      repeat rewrite homomorphic_addition_axiom.
      rewrite H0. auto.
      pose proof (IHbs u H). auto.
    Qed.
    
      
      
    Lemma tail_count_enc : forall grp bs s,
        ECount grp bs s ->
        forall us inbs m,
          s = epartial (us, inbs) m ->
          exists cs', bs = cs' ++ us /\
                 (forall c d, decrypt_message grp privatekey (m c d) =
                         decrypt_message grp privatekey (compute_margin_enc grp cs' c d)).
    Proof.
      intros grp bs s Hc.
      induction Hc; simpl; intros; inversion H; subst; clear H.
      exists []. split. auto.  simpl.
      intros. rewrite decryption_deterministic. 
      (* This goal can be discharged using axiom e1 which states that 
         decryption of m is decm *)

      pose proof (decryption_from_zkp_proof grp (m c d) (decm c d) (zkpdec c d) (e1 c d)).
      rewrite <- H. auto. 
     
      pose proof (IHHc (u :: us0) inbs0 m eq_refl).
      destruct H as [cs' [H1 H2]].
      exists (cs' ++ [u]). split. rewrite app_assoc_reverse. auto.
      intros. 
      (*  m0 : matrix_ballot_valid b it means matrix_ballot_valid u 
          so add it to the counting *)
      assert (matrix_ballot_valid (fun c d : cand => decrypt_message grp privatekey (u c d))). 
      pose proof (existence_of_perm grp cpi zkpcpi e). 
      destruct X as [[pi Hsig] Hf].
      specialize (Hf u v w zkppermuv zkppermvw e0 e1).
      destruct m0 as [Min [fn Mas]].

      assert (forall c d, decrypt_message grp privatekey (v c d) =
                     decrypt_message grp privatekey (u c (pi d))). 
      intros. pose proof (Hf c0 d0). destruct H.
      simpl in H.  assumption.
      
      assert (forall c d, decrypt_message grp privatekey (w c d) =
                     decrypt_message grp privatekey (v (pi c) d)). 
      intros. pose proof (Hf c0 d0). destruct H0. assumption.
      
      assert (forall c d, decrypt_message grp privatekey (w c d) =
                     decrypt_message grp privatekey (u (pi c) (pi d))).
      intros. rewrite H0. rewrite H. auto.
      
      assert (forall c d, b c d = decrypt_message grp privatekey (w c d)).
      intros. pose proof (decryption_from_zkp_proof grp (w c0 d0) (b c0 d0)
                                                    (zkpdecw c0 d0) (e2 c0 d0)); assumption.

      assert (forall c d, b c d = decrypt_message grp privatekey (u (pi c) (pi d))).
      intros. rewrite <- H3. auto.

      split. intros. unfold Bijective in Hsig.
      destruct Hsig as [pi_inv [Hp1 Hp2]].
      pose proof (H5 (pi_inv c0) (pi_inv d0)). rewrite Hp2 in H6. rewrite Hp2 in H6.
      rewrite <- H6. auto.
      unfold valid.  destruct Hsig as [pi_inv [Hp1 Hp2]].
      exists (fun c => fn (pi_inv c)). intros. 
      pose proof (H5 (pi_inv c0) (pi_inv d0)).
      rewrite Hp2 in H6. rewrite Hp2 in H6.  rewrite <- H6.
      pose proof (Mas (pi_inv c0) (pi_inv d0)). assumption.

      pose proof (valid_compute_margin_distributes_enc grp cs' u H).
      rewrite H0.
      rewrite e3.
      rewrite homomorphic_addition_axiom.
      rewrite homomorphic_addition_axiom.
      f_equal. apply H2.

      (* Hypothesis n states that b is not valid so it translates 
         back to decryption of u *)
      assert (Hm :
                ~matrix_ballot_valid (fun c d : cand => decrypt_message grp privatekey (u c d))).


      intro. apply n.
      unfold matrix_ballot_valid in *.
      destruct H as [H [g Hg]].

      pose proof (existence_of_perm grp cpi zkpcpi e). 
      destruct X as [[pi Hsig] Hf].
      specialize (Hf u v w zkppermuv zkppermvw e0 e1).

      assert (forall c d, decrypt_message grp privatekey (v c d) =
                     decrypt_message grp privatekey (u c (pi d))). 
      intros. pose proof (Hf c d).
      simpl in H0. destruct H0. assumption.

      assert (forall c d, decrypt_message grp privatekey (w c d) =
                     decrypt_message grp privatekey (v (pi c) d)). 
      intros. pose proof (Hf c d). simpl in H1. destruct H1. assumption.

      assert (forall c d, decrypt_message grp privatekey (w c d) =
                     decrypt_message grp privatekey (u (pi c) (pi d))).
      intros. rewrite H1. rewrite H0. auto.

      assert (forall c d, b c d = decrypt_message grp privatekey (w c d)).
      intros. pose proof (decryption_from_zkp_proof grp (w c d) (b c d) (zkpdecw c d) (e2 c d));
                assumption.

      assert (forall c d, b c d = decrypt_message grp privatekey (u (pi c) (pi d))).
      intros. rewrite H3. auto.

      split. intros. unfold Bijective in Hsig.
      destruct Hsig as [pi_inv [Hp1 Hp2]].
      rewrite H4. auto. 
      unfold valid.  destruct Hsig as [pi_inv [Hp1 Hp2]].
      exists (fun c => g (pi c)). intros.
      rewrite H4. auto. 

      
      pose proof (IHHc (u :: us0) inbs m0 eq_refl).
      destruct H as [cs' [H1 H2]].
      exists (cs' ++ [u]). split. rewrite app_assoc_reverse. auto. intros. 
      rewrite (invalid_compute_margin_same_enc _ _ _ Hm). auto. 
    Qed.
    
    
    
    

    Lemma same_margin_enc :
      forall grp bs inbs inbs0 encm encm0 s s0 (c0 : ECount grp bs s) (c1 :  ECount grp bs s0),  
        s = epartial ([], inbs) encm ->
        s0 = epartial ([], inbs0) encm0 ->
        forall c d, decrypt_message grp privatekey (encm c d) =
               decrypt_message grp privatekey (encm0 c d). 
    Proof.
      intros.
      pose proof (tail_count_enc grp bs s c0 [] inbs encm H).
      destruct H1 as [cs' [H1 H2]]. rewrite <- app_nil_end in H1.
      rewrite <- H1 in H2.
      pose proof (tail_count_enc grp bs s0 c1 [] inbs0 encm0 H0).
      destruct H3 as [cs1' [H1' H2']]. rewrite <- app_nil_end in H1'.
      rewrite <- H1' in H2'. rewrite H2, H2'. reflexivity.
    Qed.
      
      
    
    Lemma unique_dec_margin : forall grp bs dm dm0,
      ECount grp bs (edecrypt dm) ->  ECount grp bs (edecrypt dm0) ->
      dm = dm0.
    Proof.
      intros. inversion X. inversion X0. subst.
      (* The proof is if you count same set of ballots then decryption is same 
             ECount grp bs (epartial ([], inbs) encm)
             ECount grp bs (epartial ([], inbs0) encm0)
            forall c d, decryption_message grp privatekey (encm c d) = 
            forall c d, decryption_message  grp privatekey (encm0 c d) *)
      pose proof (same_margin_enc grp bs inbs inbs0 encm encm0 _ _ X1 X2 eq_refl eq_refl).
      (* From zero knowledge proof axiom, we can infer that dm is decryption of 
         encm and dm0 is decryption of encm0. By hypothesis H, we can infer that 
         dm = dm0 *)
      apply functional_extensionality; intros.
      apply functional_extensionality; intros.
      pose proof (decryption_from_zkp_proof grp (encm x x0) (dm x x0) (zkp x x0) (H0 x x0)).
      pose proof (decryption_from_zkp_proof grp (encm0 x x0) (dm0 x x0) (zkp0 x x0) (H2 x x0)).
      rewrite H1. rewrite H3.  auto. 
    Qed.
        
      
    
    Lemma uniqueness_proof_enc : forall grp bs w w',
        ECount grp bs (ewinners w) -> ECount grp bs (ewinners w') -> w = w'.
    Proof. 
      intros grp bs w w' H1 H2.
      inversion H1. inversion  H2. 
      pose proof (unique_dec_margin _ _ _ _ X X0).
      subst. apply functional_extensionality; intros.

      specialize (H3 x). specialize (H0 x). 
      specialize (H5 x). specialize (H6 x). 
      remember (w x) as Hw.
      remember (w' x) as Hw'.
      destruct Hw; destruct Hw'; try auto. 
      specialize ((proj1 H6) eq_refl); intros.
      specialize ((proj1 H0) eq_refl); intros.
      destruct H. destruct H4.
      destruct H3. destruct H5.
      pose proof (loses_type_prop dm0 x x0).
      pose proof (loses_prop_iterated_marg dm0 x H9).
      destruct H10 as [dd H10].
      pose proof (wins_type_prop dm0 x x1).
      pose proof (wins_prop_iterated_marg dm0 x H11).
      pose proof (H12 dd). omega.

      specialize ((proj1 H3) eq_refl); intros.
      specialize ((proj1 H5) eq_refl); intros.
      destruct H. destruct H4.
      destruct H3. destruct H5.
      pose proof (loses_type_prop dm0 x x0).
      pose proof (loses_prop_iterated_marg dm0 x H9).
      destruct H10 as [dd H10].
      pose proof (wins_type_prop dm0 x x1).
      pose proof (wins_prop_iterated_marg dm0 x H11).
      pose proof (H12 dd). omega.
    Qed.
      

    Lemma final_correctness_rev :
      forall  (grp : Group) (bs : list ballot) (pbs : list pballot) (ebs : list eballot)
         (w : cand -> bool)
         (H : pbs = map (fun x => (fun c d => decrypt_message grp privatekey (x c d))) ebs)
         (H2 : mapping_ballot_pballot bs pbs), (* valid b <-> valid pb *)
        ECount grp ebs (ewinners w) -> Count bs (winners w).
    Proof.
      intros grp bs pbs ebs w H0 H1 H2.
      destruct (pall_ballots_counted grp ebs) as [inb [fm Hm]]. 
      pose proof (margin_same_from_both_existential_rev
                    grp bs ebs pbs H0 H1 _ Hm [] inb []
                    (map
                       (fun (x : cand -> cand -> ciphertext)
                          (c d : cand) => decrypt_message grp privatekey (x c d)) inb)
                 fm eq_refl eq_refl eq_refl).
      destruct X as [ts [tinbs [m [[[IHc Hmm] IHm] Hw]]]].    
      assert (ts = []). destruct ts. reflexivity. inversion IHm.
      rewrite H in IHc, IHm.
      pose proof (ecdecrypt grp ebs inb fm m
                 (fun c d => construct_zero_knowledge_decryption_proof
                            grp privatekey (fm c d)) Hm).
      simpl in X.
      assert (forall c d : cand,
                 verify_zero_knowledge_decryption_proof
                   grp (m c d) (fm c d)
                   (construct_zero_knowledge_decryption_proof grp privatekey (fm c d)) = true).
      intros. apply verify_true. rewrite Hmm. auto.
      specialize (X H3). clear H3. 
      pose proof (fin bs m tinbs (c_wins m) (wins_loses_type_dec m) IHc
                      (c_wins_true_type m) (c_wins_false_type m)).
      pose proof (ecfin grp ebs m (c_wins m) (wins_loses_type_dec m)
                        X (c_wins_true_type m) (c_wins_false_type m)).
      (* I need uniqueness proof stating that 
         ECount grp ebs (ewinners w) ->  ECount grp ebs (ewinners (c_wins m)) -> 
         w = c_wins m *)  
      pose proof (uniqueness_proof_enc grp ebs _ _ H2 X1).
      rewrite H3. auto. 
    Qed.
    
    
End ECount.   
      
    
End Encryption.

Check ecount_all_ballot.

Section Candidate.

  Inductive cand := A | B | C.
  Definition cand_all := [A; B; C].

  Lemma cand_finite : forall c, In c cand_all.
  Proof.
    unfold cand_all; intro a; repeat induction a || (unfold In; tauto).
  Qed.

  Lemma  cand_eq_dec : forall c d : cand, {c = d} + {c <> d}.
  Proof.
    intros a b;
      repeat induction a; 
      repeat (induction b) || (right; discriminate) ||(left; trivial).
  Defined.

  Lemma cand_not_empty : cand_all <> nil.
  Proof. unfold cand_all. intros H. inversion H.
  Qed.
  
End Candidate.
(* 
Definition eschulze_winners_pf :=
  pschulze_winners cand cand_all cand_finite cand_eq_dec cand_not_empty. *)

Definition unicrypt_encryption_library_call :=
  ecount_all_ballot cand (group prime gen publickey).

