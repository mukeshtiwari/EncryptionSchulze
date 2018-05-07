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
Require Import Existfun.
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
      unfold listify. intros c d m.
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





  Section ECount.

    (*
    Axiom plaintext : Type.
    Axiom ciphertext : Type. *)

     
    
    Definition plaintext := Z.
    Definition ciphertext := (Z * Z)%type. (* Cipher text is pair (c1, c2). Elgamal encryption *)


    (* ballot is plain text value *)
    Definition ballot := cand -> cand -> plaintext.
    (* eballot is encrypted value *)
    Definition eballot := cand -> cand -> ciphertext.

    

    Inductive HState: Type :=
    | hpartial: (list eballot * list eballot)  ->
                (cand -> cand -> ciphertext) -> HState
    | hdecrypt: (cand -> cand -> plaintext) -> HState
    | winners: (cand -> bool) -> HState.

    (* Public key and private key are integers 
    Definition Pubkey := Z.
    Definition Prikey := Z.*)
    Axiom Pubkey : Type.
    Axiom Prikey : Type.

    (* private and public key *)
    Axiom privatekey : Prikey.
    Axiom publickey : Pubkey.


    (* This function is same as encryption function but 
       it encrypts special matrix (initial margin function)
       whose all entries are zero. We are publishing 
       encryption of this matrix and then we decrypt it with zkp
       that it is honest encryption. One superficial 
       thing with function is passing list of candidates, and 
       it is because of margin function function closure 
       which is translated back to list of values and passed to
       javaocaml binding code. *)
    Axiom encrypt_zero_margin : list cand -> Pubkey -> ballot -> eballot.

    (* This function will be realized by Elgamal Encryption.
       Enc_Pk (m, r) = (g^r, g^m * h^r). This function is not used
       but here for sake of completeness and removed in extraction*)
    Axiom encrypt_ballot : list cand -> Pubkey -> ballot ->  eballot.

    (* This function will be realized by Elgamal Decryption
       which takes encrypted message (c1, c2), private key
       and outputs the plaintext message with zkp that we have decrypted 
       the ciphertext honestly *)
    Axiom decrypt_ballot_with_zkp : list cand ->  Prikey -> eballot -> ballot * Z.

    (* This function takes encrypted ballot and returns
       row permuted reencrypted ballot with zero knowledge proof.
       For the moment, zero knowledge proof is assumed to
       be of type Z *)
    Axiom row_permute_encrypted_ballot : list cand -> Pubkey -> eballot ->  eballot * Z.

     (* This function takes row encrypted ballot and returns
       column permuted reencrypted ballot with zero knowledge proof.
       For the moment, zero knowledge proof is assumed to
       be of type Z. The two separate functions because of two 
       different implementation in Java *)
    Axiom column_permute_encrypted_ballot : list cand -> Pubkey -> eballot -> eballot * Z.
    
    (* This function takes encrypted margin function and encrypted ballot
       and multiply them pointwise. 
       https://nvotes.com/multiplicative-vs-additive-homomorphic-elgamal/ *)
    (* After Discussion with Thomas, I change it to Axiom because the multiplication
       of two big integers would be very large so either I need to pass modulas here
       or pass the data structure to Java. Second option is good 
    Definition homomorphic_add_eballots (m : cand -> cand -> ciphertext)
               (encbal : eballot)  : (cand -> cand -> ciphertext) :=
     fun c d => (fst (m c d) * fst (encbal c d), snd (m c d) * snd (encbal c d)). *)

    Axiom  homomorphic_add_eballots : list cand -> (cand -> cand -> ciphertext) ->
                                      eballot -> (cand -> cand -> ciphertext).

                                                    
                                            
    (* This function show that ciphertext (c_1, c_2) is indeed the
       the encryption of message m under zero knowledge proof. See the mail
       exchange between Dirk and Thomas Witnessing correct encryption.
       https://github.com/bfh-evg/unicrypt/blob/master/src/main/java/ch/bfh/unicrypt/crypto/proofsystem/classes/EqualityPreimageProofSystem.java
       zero_knowlege_decryption m (c_1, c_2) = true *)

    Axiom zero_knowledge_decryption_proof :
      list cand -> Pubkey -> plaintext -> ciphertext -> Z -> bool.

    

    (* This function is takes u, v and val where permute_encypted_ballot u = (v, val)
       and return true or false *)
    Axiom certify_permuted_ballots : eballot -> eballot -> Z -> bool.

    (* Note that all the assertions would be erased after code extractions
       so keeping them is kind of useless becaue we are not proving them, 
       but using a Java library, unicrypt, to plug the needed implementation.
       So in order to convince the user that it computes according to 
       logic mentioned in Coq, we are keeping data structures in inductive data type in terms of 
       zero knowledge proof which would there after extraction and could be plugged 
       into other functions to verify the correctness *)

    
    Inductive HCount (bs : list eballot) : HState -> Type :=
    (* start of counting *)
    | ax us (m : cand -> cand -> ciphertext)
         (decm : cand -> cand -> plaintext) (zkpdecm : Z)
         (* for the moment we are assuming it as integer, but it is zero knowledge proof 
            about m zero encrypted matrix *) :
        us = bs (* We start from uncounted ballots *) ->
        (* (forall c d, zero_knowledge_decryption 0 (m c d) zkpdecm = true) ->
           This is useless, because this statement is not proved in coq, but 
           will run at execution of extracted code, and should return true if 
           m is encrypted zero matrix. It helps to keep track about the
           Honest decryption proof that m is encryption of zero matrix *)
        HCount bs (hpartial (us, []) m)
    (* Valid Ballot *)
    | cvalid u (v : eballot) (w : eballot) b (zkppermuv : Z) (zkppermvw : Z)
             (zkpdecw : Z) us m nm inbs :
        HCount bs (hpartial (u :: us, inbs) m) ->
        valid cand (fun c d => b c d = 1) -> 
        (* u -> (row permutation) (v, zkppermuv) -> (column permutation) (w, zkppermvw) 
             -> (decryption of w) b.
           b is honest decryption of w proved under zero knowledge proof, zkpdecw, 
           data structure which is Z for the moment. 
           zkppermuv is zero knowledge proof data structure about v being row permutation
           of u. zkppermvw is zero knowledge proof data structre about w being column 
           permutation of v. b is valid ballot and using the lemma perm_presv_validity, it follows 
           to decryption of u.
           permute_encrypted_ballot u = (v, zkp) and ceritify_permuted_ballots u v zkp = true 
        (forall c d, (fst (permute_encrypted_ballot u)) c d = v c d /\
                     (snd (permute_encrypted_ballot u)) = zkppermuv /\
                     certify_permuted_ballots u v zkppermuv = true /\ 
                     zero_knowledge_decryption (b c d) (v c d) zkpdecv= true) -> *)
        (* Proof that new margin is encrypted sum. This statement is proved 
           in Coq, but due to mod problem, we are taking it as Axiom
        (forall c d, nm c d = homomorphic_add_eballots m u c d) -> *)
        HCount bs (hpartial (us, inbs) nm)
    (* Invalid ballot *)
    | cinvalid u (v : eballot) (w : eballot) b (zkppermuv : Z) (zkppermvw : Z)
               (zkpdecw : Z) us m inbs :
        HCount bs (hpartial (u :: us, inbs) m) ->
        ~valid cand (fun c d => b c d = 1) -> 
        (*  u -> (row permutation) (v, zkppermuv) -> (column permutation) (w, zkppermvw) 
             -> (decryption of w) b.
           b is honest decryption of w proved under zero knowledge proof, zkpdecw, 
           data structure which is Z for the moment. 
           zkppermuv is zero knowledge proof data structure about v being row permutation
           of u. zkppermvw is zero knowledge proof data structure about w being column 
           permutation of v. 
           b is invalid ballot and using the lemma not_perm_persv_validity, it follows
           to decryption of u.
        (forall c d, (fst (permute_encrypted_ballot u)) c d = v c d /\
                     (snd (permute_encrypted_ballot u)) = zkppermuv /\
                     certify_permuted_ballots u v zkppermuv = true /\
                     zero_knowledge_decryption (b c d) (v c d) zkpdecv= true) -> *)
        HCount bs (hpartial (us, u :: inbs) m) 
    (* Decrypt the margin function at this point with proof that it is
        honest decryption *)
    | cdecrypt inbs m dm (zkpdecm : Z):
        HCount bs (hpartial ([], inbs) m) ->
        (* proof of honest decryption. zkpdecm is zero knowledge proof datastructure 
           which proves that dm is decryption of m under zero knowledge proof. 
        (forall c d, zero_knowledge_decryption (dm c d) (m c d) zkpdecm = true) -> *)
        HCount bs (hdecrypt dm)
    (* Compute the winner *)
    | fin dm w (d : (forall c, (wins_type dm c) + (loses_type dm c))) :
        HCount bs (hdecrypt dm) ->
        (forall c, w c = true <-> (exists x, d c = inl x)) ->
        (forall c, w c = false <-> (exists x, d c = inr x)) ->
        HCount bs (winners w). 


    (* Each ballot is either valid or not valid *)
    Lemma ballot_valid_dec :
      forall b : ballot, {valid cand (fun c d => b c d = 1)} +
                         {~(valid cand (fun c d => b c d = 1))}.
    Proof.  
      intros b.
      pose proof (decidable_valid cand (fun c d => b c d = 1) dec_cand).
      simpl in X. assert (Ht : forall c d : cand, {b c d = 1} + {b c d <> 1}).
      intros c d. pose proof (Z.eq_dec (b c d) 1). auto.      
      pose proof (X Ht). unfold finite in X0. apply X0.
      exists cand_all. assumption.
    Defined.
    

    (* every partial state of vote tallying can be progressed to a state where
       the margin function is fully constructed, i.e. all ballots are counted *)
    
    Lemma partial_count_all_counted bs : forall ts inbs m,
        HCount bs (hpartial (ts, inbs) m) -> existsT i nm, (HCount bs (hpartial ([], i) nm)).
    Proof.
      refine (fix F ts {struct ts} :=
                match ts with
                | [] => fun inbs m Hc =>
                          existT _ inbs (existT _ m Hc)
                | u :: us =>
                  fun inbs m Hc => _
                end).
      (* We permuate the ballot u using permute_encrypted_ballot function which gives 
         permuted ballot v and zero knowledge proof of this permutation *)
      destruct (row_permute_encrypted_ballot cand_all publickey u) as [v zkppermuv].
      destruct (column_permute_encrypted_ballot cand_all publickey v) as [w zkppermvw].
      (* decrypte the permuted ballot w and prove its validity *)
      destruct (decrypt_ballot_with_zkp cand_all privatekey w) as [b zkphdec].
      (* Decide the validity of ballot b. *) 
      destruct (ballot_valid_dec b). remember (homomorphic_add_eballots cand_all m u) as nm.
      (* valid ballot so add it to encrypted marging m so far *)
      
      pose proof (F us inbs nm (cvalid bs u v w b
                                       zkppermuv (* zero knowledge proof of v being perm of u *)
                                       zkppermvw (* zero knowledge proof of w being perm of v *)
                                       zkphdec (* dummy zero knowledge proof that b is indeed correct 
                                            decryption of v *)
                                      us m nm inbs Hc v0)).  
      destruct X as [i [ns Ht]].
      exists i. exists ns. assumption.

      (* ballot not valid *) 
      pose proof (F us (u :: inbs) m
                    (cinvalid bs u v w b
                              zkppermuv (* zero knowledge proof of v being perm of u *)
                              zkppermvw (* zero knowledge proof of w being perm of v *)
                              zkphdec (* dummy zero knowledge proof that b is indeed correct 
                                   decryption of v *)
                              us m inbs Hc n)).
      destruct X as [i [ns Ht]].
      exists i. exists ns. assumption.
    Defined. 

    (* for every list of incoming ballots, we can progress the count to a state where all
     ballots are processed *)

    Lemma  all_ballots_counted (bs : list eballot) : existsT i m, HCount bs (hpartial ([], i) m).
    Proof.
      (* encrypt zero margin function *)
      pose proof (encrypt_zero_margin cand_all publickey (fun _ _ => 0)) as enczmargin.
      (* convince the user that it is indeed encryption of zero margin by decrypting it 
         and giving zero knowledge proof *)
      destruct (decrypt_ballot_with_zkp cand_all privatekey enczmargin) as [decmarg ezkp]. 
      pose proof (partial_count_all_counted bs bs [] enczmargin).
      pose (ax bs bs enczmargin decmarg
               ezkp (* Dummy Zero knowledge proof of m is zero encrypted matrix *)
               eq_refl).
      destruct (X h) as [i [m Hs]].
      exists i. exists m. assumption.
    Defined.

    
    (* We decrypt the encrypted margin to run the computation *)
    Lemma decrypt_margin (bs : list eballot) : existsT m, HCount bs (hdecrypt m).
    Proof.
      destruct (all_ballots_counted bs) as [i [encm p]].
      destruct (decrypt_ballot_with_zkp cand_all privatekey encm) as [decmarg dechzkp].
      pose proof (cdecrypt bs i encm decmarg
                          dechzkp (* Dummy Zero knowledge proof of decryption of encm *)).
      pose proof (X p).
      (* decryption of encrypted margin *)
      exists decmarg.  assumption.
    Defined.

   (* The main theorem: for every list of ballots, we can find a boolean function that decides
     winners, together with evidences of the correctness of this determination *)
    Lemma schulze_winners (bs : list eballot) :
      existsT (f : cand -> bool), HCount bs (winners f).
    Proof.
      destruct (decrypt_margin bs) as [dm H].
      exists (c_wins dm).
      pose proof (fin bs dm (c_wins dm) (wins_loses_type_dec dm)).
      pose proof (X H (c_wins_true_type dm) (c_wins_false_type dm)).
      auto.
    Defined.
    
  End ECount.

End Encryption.

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

  (*
  Inductive KPub : Type :=
  | pubkey : Z -> KPub.

  Inductive KPriv : Type :=
  | prikey : Z -> KPriv. 

  Check schulze_winners.
  
  Definition b1 : ballot cand :=
    fun c d => match c, d with
               | A, A => 0
               | A, B => 1
               | B, B => 0
               | B, A => 0
               end.


  Definition e1 : eballot cand :=
    fun c d => match c, d with
               | A, A => (0, 0)
               | A, B => (1, 0)
               | B, B => (0, 0)
               | B, A => (0, 0)
               end.
  
  
  Definition enc  (v : Pubkey) (b : ballot cand) := e1.
  Definition dec  (v : Prikey) (e : eballot cand) := b1.

  Definition dummy_fun (e : eballot cand) := (e, 0).
  Definition add_enc_marging (m : cand -> cand -> ciphertext) (e : eballot cand) :=
    fun c d : cand => match (m c d), (e c d) with
                      | (f, _), (s, _) => (f + s, 0)
                      end.
  
  Definition Schulze_all :=
    (schulze_winners cand cand_all cand_finite cand_eq_dec cand_not_empty 0 0
    enc dec dummy_fun add_enc_marging).
  

  Check Schulze_all.
  Definition bs := [e1; e1; e1; e1; e1].

  Definition schulze_win := Schulze_all bs. *)
  
End Candidate.

Definition schulze_winners_pf :=
  schulze_winners cand cand_all cand_finite cand_eq_dec cand_not_empty.


