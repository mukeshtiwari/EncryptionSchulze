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
  Section ECount. 

    (*
    Axiom Plaintext : Type.
    Axiom Ciphertext : Type. *)

    
    Definition plaintext := Z.
    Definition ciphertext := (Z * Z)%type.
    (* String is kind of hack. Cipher text is pair (c1, c2). Elgamal encryption *)
    

    (* ballot is plain text value *)
    Definition pballot := cand -> cand -> plaintext.
    (* eballot is encrypted value *)
    Definition eballot := cand -> cand -> ciphertext.
   
    
      
   
    
      
    (* Public key and private key are integers 
    Definition Pubkey := Z.
    Definition Prikey := Z.*)

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
 
    
    Axiom verify_true :
      forall (grp : Group) (pt : plaintext) (ct : ciphertext) (privatekey : Prikey)
        (H : pt = decrypt_message grp privatekey ct),
        verify_zero_knowledge_decryption_proof
          grp pt ct
          (construct_zero_knowledge_decryption_proof grp privatekey ct) = true.
    
    
    
    Inductive EState : Type :=
    | epartial : (list eballot * list eballot) ->
                 (cand -> cand -> ciphertext) -> EState
    | edecrypt : (cand -> cand -> plaintext) -> EState
    | ewinners : (cand -> bool) -> EState.
    
    Axiom Permutation : Type.
    Axiom Commitment : Type.
    Axiom ZKP : Type.
    Axiom S : Type. (* This is kind of awkward but needed because we are 
       returning S from generatePermutation function *)

    (* The idea is for each ballot u, we are going to count 
       we generate pi, cpi, and zkpcpi. We call row permute function 
       u and pi and it returns v. Then We call column permutation 
       on v and pi and it returns w. We decryp w as b with zero knowledge
       proof. *)

    (* We call a java function which returns permutation*)
    Axiom generatePermutation :
      Group -> (* group *)
      nat -> (* length  *)
      Permutation.  

    (* Pass the permutation and it returns commitment and S. The S here is bit 
       awkward but it is need when generating zero knowledge proof of commitment *)
    Axiom generatePermutationCommitment :
      Group -> (* group *)
      nat -> (* length *) 
      Permutation -> (* pi *)
      Commitment * S. (* cpi and s *)

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

    (* It does not matter how you have generted the permutation so it's better to remove the 
       hypothesis H *)
    Axiom permutation_commitment_axiom :
      forall (grp : Group) (pi : Permutation) (cpi : Commitment) (s : S)
        (zkppermcommit : ZKP) (H : pi = generatePermutation grp (List.length cand_all))
        (H1 : (cpi, s) = generatePermutationCommitment grp (List.length cand_all) pi)
        (H2 : zkppermcommit = zkpPermutationCommitment
                                grp (List.length cand_all) pi cpi s),
        verify_permutation_commitment grp (List.length cand_all)
                                      cpi zkppermcommit = true.
   
    Axiom homomorphic_addition :
      Group -> ciphertext -> ciphertext -> ciphertext.

    (* Property of Homomorphic addition *)
    Axiom homomorphic_addition_axiom :
      forall (grp : Group) (c d : cand) (u m : eballot),
      decrypt_message grp privatekey (homomorphic_addition grp (u c d) (m c d)) =
      decrypt_message grp privatekey (u c d) + decrypt_message grp privatekey (m c d).
 
   

    
    (* Start of Shuffle code *)     
    Axiom R : Type.
   
    (* eballot is cand -> cand -> ciphertext. Convert this into list (list ciphertext) 
       where each row represents preference for candidate. *)
    Axiom shuffle :
      Group -> (* group *)
      nat -> (* length *)
      list ciphertext -> (* ciphertext *)
      Permutation -> (* pi *)
      list ciphertext * R. (* shuffled ciphertext with randomness used for constructing zkp *)

    (* Construct zero knowledge proof from original and shuffled ballot *)
    Axiom shuffle_zkp :
      Group -> (* group *)
      nat -> (* length *)
      list ciphertext -> (* cipertext *)
      list ciphertext -> (* shuffle cipertext *)
      Permutation -> (* pi *)
      Commitment -> (* cpi *)
      S -> (* s, permutation commitment randomness *)
      R -> (* r, shuffle randomness *)
      ZKP. (* zero knowledge proof of shuffle *)

       
    (* verify shuffle *)
    Axiom verify_shuffle:
      Group -> (* group *)
      nat -> (* length *)
      list ciphertext -> (* cipertext *)
      list ciphertext -> (* shuffled cipertext *)
      Commitment -> (* permutation commitment *)
      ZKP -> (* zero knowledge proof of shuffle *)
      bool. (* true or false *)

   
    (* Hypothesis H can be removed *)
    Axiom verify_shuffle_axiom :
      forall (grp : Group) (pi : Permutation) (cpi : Commitment) (s : S) (cp : list ciphertext)
        (shuffledcp : list ciphertext) (r : R) (zkprowshuffle : ZKP)
        (H : pi = generatePermutation grp (List.length cand_all))
        (H1 : (cpi, s) = generatePermutationCommitment grp (List.length cand_all) pi)
        (H2 : (shuffledcp, r) = shuffle grp (List.length cand_all) cp pi)
        (H3 : zkprowshuffle = shuffle_zkp grp (List.length cand_all)
                                          cp shuffledcp pi cpi s r),
        verify_shuffle grp (List.length cand_all)
                       cp shuffledcp cpi zkprowshuffle = true.

    (* Axiom on the shuffle. This function does not change the 
       length of input list *)
    Axiom shuffle_length :
      forall (grp : Group) (n : nat) (l : list ciphertext) (pi : Permutation),
        List.length (fst (shuffle grp n l pi)) = List.length l. 

    (* end of axioms about shuffle. Discuss with Dirk, and Thomas *)     
                                                         
    
     (* A ballot is valid if all the entries are either 0 or 1 and 
        there is no cycle in ballot *)
    Definition matrix_ballot_valid (p : pballot) :=
      (forall c d : cand, In (p c d) [0; 1]) /\
      valid cand (fun c d => p c d = 1).
    Print valid.
    (* This is decibable *)
    Lemma dec_pballot :
      forall (p : pballot), 
        {forall c d : cand, In (p c d) [0; 1]} +
        {~(forall c d : cand, In (p c d) [0; 1])}.
    Proof.
    Admitted.

    
    (* mapping between ballot and pballot. This is to make sure that 
       when your ballot is valid <-> pballot is valid *)
    Definition map_ballot_pballot
               (b : ballot) (p : pballot) :=
      fun c d => if (b c <? b d)%nat &&  (0 <? b c )%nat then p c d =? 1 
                 else if (b c =? b d)%nat && (0 <? b c)%nat then p c d =? 0
                      else  if (b d <? b c)%nat && (0 <? b d)%nat then p c d =? 0
                            else p c d =? -1.

    Lemma pballot_valid_dec :
      forall b : pballot, {valid cand (fun c d => b c d = 1)} +
                     {~(valid cand (fun c d => b c d = 1))}.
    Proof.
      intros b.
      pose proof (decidable_valid cand (fun c d => b c d = 1) dec_cand).
      simpl in X. assert (Ht : forall c d : cand, {b c d = 1} + {b c d <> 1}).
      intros c d. pose proof (Z.eq_dec (b c d) 1). auto.      
      pose proof (X Ht). unfold finite in X0. apply X0.
      exists cand_all. assumption.
    Defined.

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
    

    Definition verify_row_permutation_ballot
               (u : eballot) (v : eballot)
               (cpi : Commitment) (zkppermuv : list ZKP) : bool :=
      (* This function basically transforms eballot to matrix (list (list ciphertext))
         ulist = [[], [], []], vlist = [[], [], []] and zkpermuv = [zkp1, zkp2,zkp3]
         and we call verify_shuffle with corresponding elements of 
         ulist, vlist and zkppermuv. If v is row permutation of u by pi (commitment cpi) 
         and zero knowledge proof of shuffle row_shuffle_zkp then it should return true *)
      true.

    Definition verify_col_permutation_ballot
               (v : eballot) (w : eballot)
               (cpi : Commitment) (zkppermuv  : list ZKP) : bool :=
      (* Everything like upper function except now 
         w is column permutation of v. *)
      true.

    
    
 
    
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
              (b : pballot) (zkppermuv : list ZKP)
              (zkppermvw : list ZKP) (zkpdecw : cand -> cand -> string)
              (cpi : Commitment) (zkpcpi : ZKP)
              (us : list eballot) (m nm : cand -> cand -> ciphertext)
              (inbs : list eballot) :
        ECount grp bs (epartial (u :: us, inbs) m) ->
        matrix_ballot_valid b ->
        (* commitment proof *)
        verify_permutation_commitment grp (List.length cand_all) cpi zkpcpi = true ->
        verify_row_permutation_ballot u v cpi zkppermuv = true (* cipher shuffled cpi zkp *) ->
        verify_col_permutation_ballot v w cpi zkppermvw = true (* cipher shuffled cpi zkp *) ->
        (forall c d, verify_zero_knowledge_decryption_proof 
                  grp (b c d) (w c d) (zkpdecw c d) = true) (* b is honest decryption of w *) ->
        (forall c d, nm c d = homomorphic_addition grp (u c d) (m c d)) -> 
        ECount grp bs (epartial (us, inbs) nm)
    | ecinvalid (u : eballot) (v : eballot) (w : eballot)
              (b : pballot) (zkppermuv : list ZKP)
              (zkppermvw : list ZKP) (zkpdecw : cand -> cand -> string)
              (cpi : Commitment) (zkpcpi : ZKP)
              (us : list eballot) (m : cand -> cand -> ciphertext)
              (inbs : list eballot) :
        ECount grp bs (epartial (u :: us, inbs) m) ->
        ~matrix_ballot_valid b ->
        (* commitment proof *)
        verify_permutation_commitment grp (List.length cand_all) cpi zkpcpi = true  ->
        verify_row_permutation_ballot u v cpi zkppermuv = true (* cipher shuffled cpi zkp *) ->
        verify_col_permutation_ballot v w cpi zkppermvw = true (* cipher shuffled cpi zkp *) ->
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


    (* This function constructs zero knowledge proof from 
       ballot, shuffled ballot, list of randomness r, permutation pi, p
       permutation commitment cpi and commitment randomness s *)
    Fixpoint construct_zero_knowledge_proof
             (grp : Group) (n : nat) (blt : list (list ciphertext))
             (shufblt : list (list ciphertext)) (pi : Permutation)
             (cpi : Commitment) (s : S) (rvalue : list R) :=
      match blt, shufblt, rvalue with
      | [], [], [] => []
      | [], [], _ :: _ => []
      | [], _ :: _ , [] => []
      | _ :: _, [], [] => []
      | _ :: _, _ :: _ , [] => []
      | _ :: _, [], _ :: _ => []
      | [], _ :: _, _ :: _ => []
      | h1 :: t1, h2 :: t2, r :: rt =>
        shuffle_zkp grp n
                    h1 h2 pi cpi s r ::
                    construct_zero_knowledge_proof grp n t1 t2 pi cpi s rt
      end.
                           

    
    Lemma list_not_empty :
      forall (l : list (cand * cand)), l <> [] -> existsT h t, l = h :: t.
    Proof.
      destruct l; simpl; intros; try auto.
      unfold not in H. pose proof (H eq_refl). inversion H0.
      exists p, l. auto.
    Qed.

    Lemma every_cand_t : forall (c d : cand), In (c, d) (all_pairs cand_all).
    Proof.
      intros c d. apply  all_pairsin; auto.
    Qed.

    Lemma every_cand_row : forall (c d : cand), In (c, d) (all_pairs_row cand_all).
    Proof.
      intros c d. apply all_pairs_row_in; auto.
    Qed.

    Lemma every_cand_col : forall (c d : cand), In (c, d) (all_pairs_col cand_all).
    Proof.
      intros c d. apply all_pairs_col_in; auto.
    Qed.
    
      
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
    
    
    Lemma idx_search : forall (A : Type) (c d : cand) (cl : list (cand * cand))
                         (l : list A) (Hin : In (c, d) cl)
                         (H : List.length l = List.length cl), existsT (x : A), In x l.
    Proof.
      intros A c d.  
      induction cl; simpl; intros.
      - inversion Hin.
      -  destruct l. inversion H.
         inversion H.   (* Now I want to destruct  Hin : a = (c, d) \/ In (c, d) cl 
         Case 1. Hin : a = (c, d) then I will return a0. 
         Case 2. Hin : In (c, d) l then I will apply the the induction  hypothesis 
              IHcl l Hin H1 to grab the element from existsT x : A, In x l. 
              This x is my evidence. 
              Since I have Type in Goal, so I can't destruct a Prop. 
              Is it possible to turn a = (c, d) \/ In (c, d) cl into decibable equality ? *)
         destruct (pair_cand_dec a (c, d)).
         + exists a0. intuition.
         + assert (In (c, d) cl).
           destruct Hin. contradiction. assumption.
           destruct (IHcl l H0 H1) as  [x Pr].
           exists x. intuition.
    Defined.

    
   
    Lemma flat_map_with_map_row :
      forall (l1 : list cand) (l2 : list cand ) (u : cand -> cand -> ciphertext)
        (grp : Group) (pi : Permutation), 
        List.length
          (flat_map fst
                    (map (fun x : cand =>
                            shuffle grp (List.length cand_all) (map (u x) l2) pi)
                         l1)) = ((List.length l1)%nat * (List.length l2)%nat)%nat.
    Proof.
      induction l1; simpl; intros; try auto.
      rewrite app_length, shuffle_length, map_length.
      apply f_equal.
      (* Induction Hypothesis *)
      apply IHl1.
    Qed.

    (* This duplicate lemma is needed because of my lamba function *)
    Lemma flat_map_with_map_col :
      forall (l1 l2 : list cand) (v : cand -> cand -> ciphertext)
        (grp : Group) (pi : Permutation),
        List.length
          (flat_map fst
                    (map
                       (fun c : cand =>
                          shuffle grp (Datatypes.length cand_all)
                                  (map (fun d : cand => v d c) l2) pi)
                       l1)) = ((List.length l1)%nat * (List.length l2)%nat)%nat.
    Proof.
      induction l1; simpl; intros; try auto.
      rewrite app_length, shuffle_length, map_length.
      apply f_equal.
      apply IHl1.
    Qed.
    
                                                                              
    
    
       

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
     
      (* generate permutation *) 
      remember (generatePermutation grp (List.length cand_all)) as pi.
      (* commit it *)
      remember (generatePermutationCommitment grp (List.length cand_all) pi) as cpis.
      destruct cpis as (cpi, s).
      (* generate zero knowledge proof of commitment *)
      remember (zkpPermutationCommitment grp (List.length cand_all)
                                         pi cpi s) as zkpcpi.
      (* At this point I can assert that 
         verify_permutation_commitment grp (List.length cand_all) cpi zkpcpi = true 
         using the Axiom permutation_commitment_axiom *)
      assert (verify_permutation_commitment grp (List.length cand_all) cpi zkpcpi = true).
      pose proof (permutation_commitment_axiom
                    grp pi cpi s zkpcpi Heqpi Heqcpis Heqzkpcpi). auto.
      
      (* go with list rather than vector because of extraction *) 
      (* Construct each row *)
      remember (map (fun c => u c) cand_all) as partialballot. 
      (* construct the orignal ballot because it's needed for zkp construction *)
      remember (map (fun b => map b cand_all) partialballot) as nballot.
      (* construct suffled ballot. for each row do rowshuffle *)
      remember (map (fun b => shuffle grp (List.length cand_all)
                                   (map b cand_all) pi) partialballot) as rowShuffledwithR. 
      remember (map fst rowShuffledwithR) as rowshuffled.
      remember (map snd rowShuffledwithR) as rvalues.
      (* Now I have row shuffled ballot by pi, construct zero knowledge proof *)
      remember (construct_zero_knowledge_proof
                  grp (List.length cand_all)
                  nballot rowshuffled pi cpi s rvalues) as zkppermuv.
      
      (* Now convert the rowshuffled ballot into function closure *)
      assert (List.length (List.concat rowshuffled) = List.length (all_pairs_row cand_all)).
      rewrite Heqrowshuffled. rewrite <- (flat_map_concat_map _ rowShuffledwithR).
      rewrite HeqrowShuffledwithR. rewrite Heqpartialballot.
      rewrite (map_map _ _ cand_all).
      rewrite length_all_pairs_row.
      pose proof (flat_map_with_map_row cand_all cand_all u grp pi). auto.
      (* Finally, I am feeling good :) *)
      (* Construct function closure v from rowshuffled list *)
      remember (fun (c d : cand) =>
                  match (idx_search _ c d
                                    (all_pairs_row cand_all)(* This would generate in row order *)
                                    (List.concat rowshuffled) (* concat each row *)
                                    (every_cand_row c d) H0) with
                  | existT _  f _ => f
                  end) as v.
      (* Show that verify_row_permutation_ballot u v cpi zkppermuv return true.
         The property here is construct matrix from u and v and comp
         This is bit tricky so I am leaving it for the moment because we need to 
         massage the axioms *)
      assert (Ht1 : verify_row_permutation_ballot u v cpi zkppermuv = true). admit.
      
      (* Now I have rowshuffled ballot in form of function closure, 
         Now apply column shuffle on this ballot. Change the name of 
         row_shuffle to shuffle to avoid the confusion*)
      (* Construct the normal ballot in column form for zero knowledge proof construction *)
      remember (map (fun c => map (fun d => v d c) cand_all) cand_all) as colballot.
      remember (map (fun c =>
                       shuffle grp
                               (List.length cand_all)
                               (map (fun d => v d c) cand_all) pi) cand_all) as colShufflewithR.
      remember (map fst colShufflewithR) as colShuffledballot.
      remember (map snd colShufflewithR) as rcolvalues.
      remember (construct_zero_knowledge_proof
                  grp (List.length cand_all)
                  colballot colShuffledballot pi cpi s rcolvalues) as zkppermvw.
      (* Now convert colshuffledballot into function closure *)
      (* The problem is that each element of colshuffledballot is column of 
         rowshuffle ballot. I want to change it in function closure without 
         changing the structure of ballot. The idea is write another function 
         similiar to all_pairs_row but produce results in column form. 
         Let's say [A, B, C] => all_pairs_row would produce
         [AA, AB, AB, BA, BB, BC, CA, CB, CC] so it would kind of mismatch the 
         ballot with idx_search. 
         Write a new function all_pair_col [A, B, C] => 
         [AA, BA,  CA, AB, BB, CB, AC, BC, CC] and call this value with 
         List.concat (colshuffledballot) to make sure that structure presevers. *)
      (* Now I have solved the problem by writing different functions for row and column *)

      assert (Datatypes.length (concat colShuffledballot) =
              Datatypes.length (all_pairs_col cand_all)).
      rewrite HeqcolShuffledballot.
      rewrite <- (flat_map_concat_map _ colShufflewithR).
      rewrite HeqcolShufflewithR. rewrite length_all_pairs_col.
      pose proof (flat_map_with_map_col cand_all cand_all v grp pi). auto.            
      remember (fun (c d : cand) =>
                  match (idx_search _ c d
                                    (all_pairs_col cand_all)(* This would generate in col order *)
                                    (List.concat colShuffledballot) (* concat each row *)
                                    (every_cand_col c d) H1 ) with
                  | existT _  f _ => f
                  end) as w.
      (*  Show that verify_col_permutation_ballot v w cpi zkppermvw return true. 
         This is bit tricky so I am leaving it for the moment because we need to 
         massage the axioms *)
      assert (Ht2 : verify_col_permutation_ballot v w cpi zkppermvw = true). admit.
      
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
    Admitted.
    

      
      

     
     


     (* for every list of incoming ballots, we can progress the count to a state where all
     ballots are processed *)
    Lemma  pall_ballots_counted (grp : Group) (bs : list eballot) :
      existsT i m, ECount grp bs (epartial ([], i) m).
    Proof.
      pose proof (ecount_all_ballot grp bs) as Hs.
      destruct Hs as [encm Heg].
      pose proof (ppartial_count_all_counted grp bs bs [] encm Heg).
      auto. (* Try to see this if anything goes wrong *)
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


    (* Now Try to prove that result computed by schulze_winner 
       pschulze_winners are same if ballots match *)

    (* This function connects the ballot and pballot. pballot is decryption of eballot *)
    (*
    Inductive mapping_ballot_pballot : list ballot -> list pballot -> Prop :=
    | firstcons : mapping_ballot_pballot [] []
    | secondcons h1 h2 t1 t2 :
        (forall c d, map_ballot_pballot h1 h2 c d = true) -> mapping_ballot_pballot t1 t2 ->
        mapping_ballot_pballot (h1 :: t1) (h2 :: t2). *)
   
    Fixpoint mapping_ballot_pballot (bs : list ballot) (pbs : list pballot) : Prop. 
    Proof.
      refine (match bs, pbs with
              | [], [] => True
              | [], h :: _ => False 
              | h :: _, [] => False
              | h1 :: t1, h2 :: t2 =>
                ((forall c d, map_ballot_pballot h1 h2 c d = true) /\
                 mapping_ballot_pballot t1 t2 )
              end); inversion H.
    Defined.

    (* Validity connection of ballot and pballot *)
    Lemma connect_validity_of_ballot_pballot :
      forall (b : ballot) (p : pballot),
        (forall c d, map_ballot_pballot b p c d = true) -> 
        proj1_sig (bool_of_sumbool (ballot_valid_dec b)) = true <->
        proj1_sig (bool_of_sumbool (matrix_ballot_valid_dec p)) = true.
    Proof. 
      intros b p Hm. split; intros.
      destruct (ballot_valid_dec b) as [H1 | H2];
        destruct (matrix_ballot_valid_dec p) as [Hp1 | Hp2]; simpl in *; try auto. 
      (* This is not valid, because if b c > 0 then it means P c d = 0 \/ P c d = 1*) 
      unfold map_ballot_pballot in Hm. 
      destruct Hp2. unfold matrix_ballot_valid. 
      split. intros.  simpl.
      pose proof (Hm c d). pose proof (H1 c). Open Scope nat_scope.
      assert (0 < b c) by omega.
      pose proof (proj2 (Nat.ltb_lt _ _) H3). 
      rewrite H4 in H0. rewrite (andb_true_r (b c <? b d)) in H0.
      pose proof (H1 d). pose proof (lt_eq_lt_dec (b c) (b d)).
      destruct H6 as [[H6 | H6] | H6].
      pose proof (proj2 (Nat.ltb_lt _ _) H6).
      rewrite H7 in H0.  apply Z.eqb_eq in H0. auto.
      (* since b c = b d it means b c <? b d = false and b c ?= b d = true *)
      remember (b c <? b d) as v.
      symmetry in Heqv. destruct v.
      pose proof (proj1 (Nat.ltb_lt _ _) Heqv). omega.
      pose proof (proj2 (Nat.eqb_eq _ _) H6).
      rewrite H7 in H0. simpl in H0.  apply  Z.eqb_eq in H0. auto.
      assert (b c <? b d = false).
      apply Nat.ltb_ge. omega. rewrite H7 in H0.
      assert ((b c =? b d)%nat = false).
      apply Nat.eqb_neq. omega.
      rewrite H8 in H0. simpl in H0. 
      pose proof(proj2 (Nat.ltb_lt _ _) H6).
      assert (0 < b d) by omega.
      pose proof (proj2 (Nat.ltb_lt _ _) H10).
      rewrite H9 in H0. rewrite H11 in H0. simpl in H0. apply Z.eqb_eq in H0. auto.
           
      (* discharge the validity *) 
      exists b.  intros c d. split; intros.
      pose proof (H1 c). pose proof (H1 d).
      assert (0 < b c) by omega.
      pose proof (proj2 (ltb_lt _ _) H4).
      pose proof (Hm c d).
      rewrite H5 in H6. 
      rewrite (andb_true_r (b c <? b d)) in H6.
      rewrite (andb_true_r (b c =? b d)) in H6.  
      (* God, give me strength to discharge all the menial proofs *)
      pose proof (lt_eq_lt_dec (b c) (b d)).
      destruct H7 as [[H7 | H7] | H7]. auto.
      rewrite H7 in H6.
      rewrite (Nat.ltb_irrefl (b d)) in H6.
      rewrite (Nat.eqb_refl (b d)) in H6.
      apply Z.eqb_eq in H6.
      rewrite H6 in H0. inversion H0. 
      remember (b c <? b d) as v. symmetry in Heqv.
      destruct v. 
      pose proof (proj1 (Nat.ltb_lt (b c) (b d)) Heqv). omega.
      remember (b c =? b d) as v. symmetry in Heqv0.
      destruct v. apply Z.eqb_eq in H6. rewrite H6 in H0. inversion H0.
      pose proof (proj2 (Nat.ltb_lt (b d) (b c)) H7). rewrite H8 in H6.
      assert (0 < b d) by omega.
      pose proof (proj2 (Nat.ltb_lt 0 (b d)) H9). rewrite H10 in H6.
      simpl in H6. apply Z.eqb_eq in H6. rewrite H6 in H0. inversion H0.
      (* Thank you God for giving me strenght *)      
      pose proof (Hm c d).
      pose proof (H1 c).
      pose proof (proj2 (Nat.ltb_lt (b c) (b d)) H0). rewrite H4 in H2.
      pose proof (proj2 (Nat.ltb_lt 0 (b c))).
      assert (0 < b c) by omega. pose proof (H5 H6). 
      rewrite H7 in H2. simpl in H2.  apply Z.eqb_eq in H2. auto.
        
      (* Other side of proof. When pballot is valid then ballot is also 
         valid *)
      destruct (matrix_ballot_valid_dec p) as [H1 | H2];
        destruct (ballot_valid_dec b) as [Hp1 | Hp2]; simpl in *; try (auto with arith).
      (* Now this case invalid because my pballot is valid and b is invalid *)  
      destruct Hp2. unfold valid in H1. destruct H1 as [Hin [f H1]].
      unfold map_ballot_pballot in Hm.     
      pose proof (Hm x).
      rewrite H0 in H2. 
      rewrite (Nat.ltb_irrefl 0) in H2. 
      pose proof (H2 x).  rewrite (andb_false_r (0 <? b x)) in H3.
      rewrite (andb_false_r (0 =? b x)) in H3.
      rewrite H0 in H3. simpl in H3. pose proof (Hin x x).
      destruct H4. apply Z.eqb_eq in H3. rewrite H3 in H4. inversion H4.
      destruct H4. apply Z.eqb_eq in H3. rewrite H3 in H4. inversion H4. auto.
    Qed.
    
    Lemma connect_invalidity_of_ballot_pballot :
      forall (b : ballot) (p : pballot),
        (forall c d, map_ballot_pballot b p c d = true) -> 
        proj1_sig (bool_of_sumbool (ballot_valid_dec b)) = false <->
        proj1_sig (bool_of_sumbool (matrix_ballot_valid_dec p)) = false.
    Proof.
      intros b p Hm. split; intros. 
      destruct (ballot_valid_dec b) as [H1 | H2];
        destruct (matrix_ballot_valid_dec p) as [Hp1 | Hp2]; simpl in *; try auto.
      unfold map_ballot_pballot in Hm. destruct H2 as [c H2].
      unfold matrix_ballot_valid in Hp1. destruct Hp1 as [Hp1l Hp2r].
      (* Since b c = 0 *)
      specialize (Hm c c). 
      assert (0 <? b c = false). apply Nat.ltb_ge. omega.
      rewrite H0 in Hm. rewrite andb_false_r in Hm.
      rewrite andb_false_r in Hm.  apply Z.eqb_eq in Hm.
      specialize (Hp1l c c). destruct Hp1l. rewrite <- H1 in Hm.
      inversion Hm. simpl in H1. destruct H1.
      rewrite <- H1 in Hm. inversion Hm. inversion H1.
       
      (* Other side of proof *)
      destruct (matrix_ballot_valid_dec p) as [H1 | H1];
        destruct (ballot_valid_dec b) as [Hp | Hp]; simpl in *; try auto.
      destruct H1. unfold matrix_ballot_valid. split; intros.
      unfold map_ballot_pballot in Hm.
      specialize (Hm c d).
      pose proof (Hp c). pose proof (Hp d).
      assert (0 < b c) by omega. clear H0.
      assert (0 < b d) by omega. clear H1.
      pose proof (proj2 (Nat.ltb_lt _ _) H2).
      pose proof (proj2 (Nat.ltb_lt _ _) H0). 
      pose proof (lt_eq_lt_dec (b c) (b d)).
      destruct H4 as [[H4 | H4] | H4].
      pose proof (proj2 (Nat.ltb_lt _ _) H4).
      rewrite H1 in Hm. rewrite H5 in Hm.
      simpl in Hm. apply Z.eqb_eq in Hm.
      simpl. auto.
      (* b c = b d it means b c <? b d = false and b c ?= b d = true  *)
      remember (b c <? b d) as v.
      symmetry in Heqv. destruct v.
      pose proof (proj1 (Nat.ltb_lt _ _) Heqv). omega.
      simpl in Hm. pose proof (proj2 (Nat.eqb_eq _ _) H4).
      rewrite H5 in Hm. rewrite H1 in Hm. simpl in *.
      apply Z.eqb_eq in Hm. auto.
      assert (b c <? b d = false).  apply Nat.ltb_ge. omega.
      rewrite H5 in Hm. simpl in Hm.
      assert ((b c =? b d)%nat = false).
      apply Nat.eqb_neq. omega. rewrite H6 in Hm. simpl in Hm.
      pose proof(proj2 (Nat.ltb_lt _ _) H4). rewrite H7 in Hm.
      rewrite H3 in Hm. simpl in *.
      apply Z.eqb_eq in Hm. auto.
      (* discharge the validity proof *) 
      unfold valid. exists b. intros c d. split; intros.
      pose proof (Hp c). pose proof (Hp d).
      assert (0 < b c) by omega.
      assert (0 < b d) by omega. clear H1. clear H2.
      pose proof (proj2 (ltb_lt _ _) H3).
      pose proof (proj2 (ltb_lt _ _) H4).
      specialize (Hm c d). 
      unfold map_ballot_pballot in Hm. 
      pose proof (lt_eq_lt_dec (b c) (b d)).
      destruct H5 as [[H5 | H5] | H5].
      auto.
      remember (b c <? b d) as v. symmetry in Heqv.
      destruct v. 
      pose proof (proj1 (Nat.ltb_lt (b c) (b d)) Heqv). omega.
      simpl in Hm. 
      remember (b c =? b d) as v. symmetry in Heqv0.
      destruct v. rewrite H1 in Hm. simpl in Hm. apply Z.eqb_eq in Hm.
      rewrite Hm in H0. inversion H0.
      simpl in Hm.
      assert (b d <? b c = false). rewrite H5.
      apply Nat.ltb_irrefl.
      rewrite H6 in Hm. simpl in Hm.
      apply Z.eqb_eq in Hm. rewrite Hm in H0. inversion H0.
      assert (b c <? b d = false).
      apply Nat.ltb_ge. omega. rewrite H6 in Hm. simpl in Hm.
      clear H6.  assert ((b c =? b d)%nat = false).
      apply Nat.eqb_neq. omega.
      rewrite H6 in Hm. simpl in Hm. rewrite H2 in Hm.
      apply Nat.ltb_lt in H5. rewrite H5 in Hm. simpl in Hm.
      apply Z.eqb_eq in  Hm. rewrite Hm in H0. inversion H0.

      specialize (Hm c d). unfold map_ballot_pballot in Hm.
      pose proof (Hp c). pose proof (proj2 (Nat.ltb_lt (b c) (b d)) H0).
      rewrite H2 in Hm. pose proof (proj2 (Nat.ltb_lt 0 (b c))).
      assert (0 < b c) by omega. specialize (H3 H4).
      rewrite H3 in Hm. simpl in Hm. apply Z.eqb_eq in Hm.
      assumption.
    Qed.
    

      
    (* One to One correspondence *)
    Lemma mapping_ballot_pballot_equality :
      forall (xs : list ballot) (ys : list pballot)
        (zs : list pballot),
        mapping_ballot_pballot xs ys -> mapping_ballot_pballot xs zs -> ys = zs.
    Proof.      
      induction xs. intros.
      destruct ys, zs. auto. simpl in H0. inversion H0.
      simpl in H. inversion H. simpl in H. inversion H.
      (* Inductive case *)
      intros. simpl in H. simpl in H0.
      destruct ys, zs. auto. inversion H. inversion H0.
      destruct H. destruct H0.
      assert (forall c d, p c d = p0 c d).
      intros. specialize (H c d).
      specialize (H0 c d).
      unfold map_ballot_pballot in H.
      unfold map_ballot_pballot in H0.
      pose proof (zerop (a c)). destruct H3.
      assert ((0 <? a c)%nat = false).
      rewrite e. SearchAbout (_ <? _ = false)%nat.
      apply Nat.ltb_irrefl.  rewrite H3 in H.
      rewrite H3 in H0.
      rewrite andb_false_r in H.
      rewrite andb_false_r in H.
      rewrite andb_false_r in H0.
      rewrite andb_false_r in H0.
      pose proof (zerop (a d)). destruct H4.
      assert ((0 <? a d)%nat = false). rewrite e0.
      apply Nat.ltb_irrefl. rewrite H4 in H.
      rewrite H4 in H0. rewrite andb_false_r in H.
      rewrite andb_false_r in H0.
      SearchAbout ( _ =? _ = true).
      apply Z.eqb_eq in H. apply Z.eqb_eq in H0.
      rewrite H. rewrite H0. auto.
      assert ((a d <? a c)%nat = false).
      rewrite e. SearchAbout (_ <? _ )%nat.
      apply Nat.ltb_nlt. unfold not. intros.
      omega. rewrite H4 in H. rewrite H4 in H0.
      rewrite andb_false_l in H.
      rewrite andb_false_l in H0.
      apply Z.eqb_eq in H. apply Z.eqb_eq in  H0.
      rewrite H. rewrite H0. auto.
      assert ((0 <? a c)%nat = true).
      SearchAbout ( _ <? _ = true)%nat.
      apply Nat.ltb_lt. auto. rewrite H3 in H.
      rewrite H3 in H0.
      rewrite andb_true_r in H.
      rewrite andb_true_r in H.
      rewrite andb_true_r in H0.
      rewrite andb_true_r in H0.
      pose proof (lt_eq_lt_dec (a c) (a d)).
      destruct H4 as [[H4 | H4] | H4].
      assert ((a c <? a d)%nat = true).
      SearchAbout (_ <? _ = true)%nat.
      apply Nat.ltb_lt. auto. rewrite H5 in H.
      rewrite H5 in H0.
      apply Z.eqb_eq in H. apply Z.eqb_eq in H0.
      rewrite H. rewrite H0. auto.
      assert ((a c <? a d)%nat = false).
      SearchAbout (_ <? _ = false)%nat.
      apply Nat.ltb_nlt. unfold not. intros.
      omega. rewrite H5 in H.
      rewrite H5 in H0.
      assert ((a c =? a d)%nat = true).
      SearchAbout (_ =? _ = true)%nat.
      apply Nat.eqb_eq. auto.
      rewrite H6 in H. rewrite H6 in H0.
      apply Z.eqb_eq in H. apply Z.eqb_eq in H0.
      rewrite H. rewrite H0. auto.
      assert ((a c <? a d)%nat = false).
      SearchAbout (_ <? _ = false)%nat.
      apply Nat.ltb_nlt. unfold not. intros.
      omega. rewrite H5 in H. rewrite H5 in H0.
      assert ((a c =? a d)%nat = false).
      SearchAbout (_ =? _ = false).
      apply Nat.eqb_neq. unfold not. intros. omega.
      rewrite H6 in H. rewrite H6 in H0.
      assert ((a d <? a c)%nat = true).
      apply Nat.ltb_lt. auto. rewrite H7 in H.
      rewrite H7 in H0.
      rewrite andb_true_l in H. rewrite andb_true_l in H0.
      pose proof (zerop (a d)). destruct H8.
      assert ((0 <? a d)%nat = false).
      apply Nat.ltb_nlt. unfold not. intros.
      omega. rewrite H8 in H. rewrite H8 in H0.
      apply Z.eqb_eq in H. apply Z.eqb_eq in H0.
      rewrite H. rewrite H0. auto.
      assert ((0 <? a d)%nat = true).
      apply Nat.ltb_lt. auto. rewrite H8 in H.
      rewrite H8 in H0. apply Z.eqb_eq in H.
      apply Z.eqb_eq in H0. rewrite H. rewrite H0. auto.
      (* I need functional extensionality. Discuss this with Dirk *)
      Require Import Coq.Logic.FunctionalExtensionality.
      assert (p = p0).
      apply functional_extensionality.
      intros x. apply functional_extensionality.
      intros x0. auto.
      (* End of extensionality *)
      rewrite H4. apply f_equal. apply IHxs. auto. auto.
    Qed.

    Lemma map_map_l :
      forall (A B : Type) (l1 l2 : list A) (f : A -> B),
        map f l1 = map f l2 -> l1 = l2.
    Proof.
      intros A B. induction l1; simpl; intros.
      - symmetry in H. apply map_eq_nil in H. auto.
      - destruct l2.
        -- inversion H.
        -- simpl in H. inversion H.
           (* This can't be inferred until function is one one onto function *)
    Admitted. 
    

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
      intros. inversion H0. 
      specialize (IHCount (u :: us) inbs m eq_refl). 
      destruct IHCount as [ets [etinbs [tbps [etpbs [em H6]]]]].
      destruct H6. destruct p. destruct p. destruct p. destruct p.
      (* From m2 we can infer that tbps <> [] and it can be written as 
         tbps = t :: tpbs'. From this statement we can infer that ets <> [] using e0.
         ets = e :: ets'. 
         u is valid => t valid => it's decryption is also valid 
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
      (* commit it *)
      remember (generatePermutationCommitment grp (List.length cand_all) pi) as cpis.
      destruct cpis as (cpi, s).
      (* generate zero knowledge proof of commitment *)
      remember (zkpPermutationCommitment grp (List.length cand_all)
                                         pi cpi s) as zkpcpi. 
      (* At this point I can assert that 
         verify_permutation_commitment grp (List.length cand_all) cpi zkpcpi = true 
         using the Axiom permutation_commitment_axiom *)
      assert (verify_permutation_commitment grp (List.length cand_all) cpi zkpcpi = true).
      pose proof (permutation_commitment_axiom
                    grp pi cpi s zkpcpi Heqpi Heqcpis Heqzkpcpi). auto.
      (* Construct each row *)
      remember (map (fun c => en c) cand_all) as partialballot. 
      (* construct the orignal ballot because it's needed for zkp construction *)
      remember (map (fun b => map b cand_all) partialballot) as nballot.
      (* construct suffled ballot. for each row do rowshuffle *)
      remember (map (fun b => shuffle grp (List.length cand_all)
                                   (map b cand_all) pi) partialballot) as rowShuffledwithR. 
      remember (map fst rowShuffledwithR) as rowshuffled.
      remember (map snd rowShuffledwithR) as rvalues.
      (* Now I have row shuffled ballot by pi, construct zero knowledge proof *)
      remember (construct_zero_knowledge_proof
                  grp (List.length cand_all)
                  nballot rowshuffled pi cpi s rvalues) as zkppermuv.
      (* Now convert the rowshuffled ballot into function closure *)
      assert (List.length (List.concat rowshuffled) = List.length (all_pairs_row cand_all)).
      rewrite Heqrowshuffled. rewrite <- (flat_map_concat_map _ rowShuffledwithR).
      rewrite HeqrowShuffledwithR. rewrite Heqpartialballot.
      rewrite (map_map _ _ cand_all).
      rewrite length_all_pairs_row.
      pose proof (flat_map_with_map_row cand_all cand_all en grp pi). auto.
      (* Construct function closure v from rowshuffled list *)
      remember (fun (c d : cand) =>
                  match (idx_search _ c d
                                    (all_pairs_row cand_all)(* This would generate in row order *)
                                    (List.concat rowshuffled) (* concat each row *)
                                    (every_cand_row c d) H10) with
                  | existT _  f _ => f
                  end) as v.
      (* Show that verify_row_permutation_ballot en v cpi zkppermuv return true.
         The property here is construct matrix from u and v and comp
         This is bit tricky so I am leaving it for the moment because we need to 
         massage the axioms *)
      assert (Ht1 : verify_row_permutation_ballot en v cpi zkppermuv = true). admit.
      (* Construct the normal ballot in column form for zero knowledge proof construction *)
      remember (map (fun c => map (fun d => v d c) cand_all) cand_all) as colballot.
      remember (map (fun c =>
                       shuffle grp
                               (List.length cand_all)
                               (map (fun d => v d c) cand_all) pi) cand_all) as colShufflewithR.
      remember (map fst colShufflewithR) as colShuffledballot.
      remember (map snd colShufflewithR) as rcolvalues.
      remember (construct_zero_knowledge_proof
                  grp (List.length cand_all)
                  colballot colShuffledballot pi cpi s rcolvalues) as zkppermvw.
      assert (Datatypes.length (concat colShuffledballot) =
              Datatypes.length (all_pairs_col cand_all)).
      rewrite HeqcolShuffledballot.
      rewrite <- (flat_map_concat_map _ colShufflewithR).
      rewrite HeqcolShufflewithR. rewrite length_all_pairs_col.
      pose proof (flat_map_with_map_col cand_all cand_all v grp pi). auto.            
      remember (fun (c d : cand) =>
                  match (idx_search _ c d
                                    (all_pairs_col cand_all)(* This would generate in col order *)
                                    (List.concat colShuffledballot) (* concat each row *)
                                    (every_cand_col c d) H11) with
                  | existT _  f _ => f
                  end) as w.
      (*  Show that verify_col_permutation_ballot v w cpi zkppermvw return true. 
         This is bit tricky so I am leaving it for the moment because we need to 
         massage the axioms *)
      assert (Ht2 : verify_col_permutation_ballot v w cpi zkppermvw = true). admit.
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
         H2 : forall c d : cand, map_ballot_pballot u t c d = true
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
      assert (matrix_ballot_valid b). admit.
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
      pose proof (homomorphic_addition_axiom grp x x0 en em).
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
      pose proof (H2 x x0). unfold map_ballot_pballot in H20.
      pose proof (g x). pose proof (g x0).
      assert (0 < u x) by omega.
      assert (0 < u x0) by omega.
      
      

      auto. auto. rewrite H3 in H8. auto.
      rewrite H4 in m1. auto.
      



     
















      
      
         
      
    Lemma margin_same_from_both 
          (grp : Group) (bs : list ballot) (ebs : list eballot) (pbs : list pballot)
          (Ht : pbs = map (fun x => (fun c d => decrypt_message grp privatekey (x c d))) ebs)
          (H1 : mapping_ballot_pballot bs pbs) :
      forall (s : State),
        Count bs s ->
        forall (ts : list ballot) (tinbs : list ballot)
          (ets : list eballot) (etinbs : list eballot)
          (tpbs : list pballot) (etpbs : list pballot)
          (em : cand -> cand -> ciphertext)
          (H2 : tpbs =  map (fun x => (fun c d => decrypt_message grp privatekey (x c d))) ets)
          (H3 : etpbs =  map (fun x => (fun c d => decrypt_message grp privatekey (x c d))) etinbs)
          (H4 : mapping_ballot_pballot ts tpbs)
          (H5 : mapping_ballot_pballot tinbs etpbs ),
          s = partial (ts, tinbs) (fun c d => decrypt_message grp privatekey (em c d)) ->
          ECount grp ebs (epartial (ets, etinbs) em).
    Proof. 
      intros s H.   
      (* Induction on strucutre of H *)
      induction H. intros.  inversion H.
      (* Now I have to show to one to one correspondence between Count and ECount. 
         Basically it's more like margins computation is same in both data types *)
      pose proof (ecax grp ebs ebs em m
                       (fun c d => construct_zero_knowledge_decryption_proof
                                  grp privatekey (em c d)) eq_refl e0). 
      simpl in X.
      assert (forall c d : cand,
                 verify_zero_knowledge_decryption_proof
                   grp (m c d) (em c d)
                   (construct_zero_knowledge_decryption_proof grp privatekey (em c d)) = true).
      intros. subst. apply verify_true. auto.
      specialize (X H0).   
      (* Assert that if tinbs is empty then encryption of tinbs i.e. etinbs = [] *)
      rewrite <- H7 in H5.
      assert (etpbs = []). destruct etpbs; try auto.
      inversion H5. rewrite H9 in H3. symmetry in H3.
      apply map_eq_nil in H3. rewrite H3.
      assert (ebs = ets).
      rewrite <- H6 in H4.
      rewrite <- e in H1.
      pose proof (mapping_ballot_pballot_equality _ _ _ H1 H4).
      rewrite Ht in H10. rewrite H2 in H10. 
      (* This goal is not provable because two different lists
         can be decrypt to same value, not necessary they have to be the 
         same. I encountered this problem, so rather than assuming 
         us = bs, 
         assume they decrypt to same plaintext
         map (fun x : eballot => fst (decrypt_ballot_with_zkp cand_all privatekey x)) us = 
         map (fun x : eballot => fst (decrypt_ballot_with_zkp cand_all privatekey x)) bs.
         Admit it and discuss with Dirk *)
      admit.
      rewrite <- H10. assumption. 

      (*Count bs (partial (u :: us, inbs) m) *)
      (* Take ballot u, convert it into matrix form, 
         test the validity of u, show that validity of u connects with 
         validity of matrix form. 
       1. If u is valid <-> umat is valid
          add u to margin m <-> homomorphic add encryption of umat to
                                encryption of m. *)
      intros. inversion H0.  
      (* change u to matrix form and decide validity.*)
      Open Scope Z.
      remember (fun c d =>
                  if (u c <? u d)%nat &&  (0 <? u c )%nat then 1 
                  else if (u c =? u d)%nat && (0 <? u c)%nat then  0
                       else  if (u d <? u c)%nat && (0 <? u d)%nat then 0
                             else -1) as umat. 
      (* Show that they are equivalent *)
      pose proof (connect_validity_of_ballot_pballot u umat).
      assert (forall c d : cand, map_ballot_pballot u umat c d = true).
      intros c d. unfold map_ballot_pballot.
      remember (umat c d) as tumat.
      rewrite Hequmat in Heqtumat.
      destruct ((u c <? u d)%nat && (0 <? u c)%nat) in *.
      apply Z.eqb_eq in Heqtumat. auto.
      destruct ((u c =? u d)%nat && (0 <? u c)%nat).
      apply Z.eqb_eq in Heqtumat. auto.
      destruct ((u d <? u c)%nat && (0 <? u d)%nat).
      apply Z.eqb_eq in Heqtumat. auto.
      apply Z.eqb_eq in Heqtumat. auto.
      specialize (H6 H10).
      (* valid b <-> valid u *)
      destruct H6 as [H11 H12].
      (* assert that u is valid. See hypothesis g and a *)
      assert (proj1_sig (bool_of_sumbool (ballot_valid_dec u)) = true).
      destruct (ballot_valid_dec u); simpl; try auto.
      destruct e as [c Hu].
      pose proof (g c); try omega. 
      specialize (H11 H6). 
      specialize (IHCount (u :: us) inbs
                          ((fun c d => encrypt_message grp (umat c d)) :: ets) etinbs
                          (umat :: tpbs) etpbs
                          (fun c d => encrypt_message grp (m c d))).
      simpl in IHCount.
      assert ( umat :: tpbs =
               (fun c d : cand => decrypt_message grp privatekey (encrypt_message grp (umat c d)))
                 :: map
                 (fun (x : cand -> cand -> ciphertext) (c d : cand) =>
                    decrypt_message grp privatekey (x c d)) ets).
      assert (umat =
              (fun c d => decrypt_message grp privatekey (encrypt_message grp (umat c d)))).
      Require Import Coq.Logic.FunctionalExtensionality.
      apply functional_extensionality. intros.
      apply functional_extensionality. intros.
      rewrite decryption_deterministic. auto.
      rewrite <- H13. apply f_equal. auto.
      specialize (IHCount H13 H3). clear H13.
      assert ((forall c d : cand, map_ballot_pballot u umat c d = true) /\
              mapping_ballot_pballot us tpbs).
      split. auto. rewrite <- H7 in H4. auto.
      specialize (IHCount H13). clear H13.
      rewrite <- H8 in H5.
      specialize (IHCount H5).
      assert (m = (fun c d : cand => decrypt_message grp privatekey (encrypt_message grp (m c d)))).
      apply functional_extensionality. intros.
      apply functional_extensionality. intros.
      rewrite decryption_deterministic. auto.
      rewrite <- H13 in IHCount.
      specialize (IHCount eq_refl).
      (* Now I have contructed 
          ECount grp ebs
              (epartial ((fun c d : cand => encrypt_message grp (umat c d)) :: ets, etinbs)
                 (fun c d : cand => encrypt_message grp (m c d))). 
         From This state I count the ballot umat because it's valid, and move on 
         use ecvalid to proceed *)
      pose proof(ecvalid grp ebs).
      remember (fun c d : cand => encrypt_message grp (umat c d)) as uenc.
      (* instantiate u with uenc. *)
      (* This is same as  ppartial_count_all_counted  *)
      (* generate permutation *) 
      remember (generatePermutation grp (List.length cand_all)) as pi.
      (* commit it *)
      remember (generatePermutationCommitment grp (List.length cand_all) pi) as cpis.
      destruct cpis as (cpi, s).
      (* generate zero knowledge proof of commitment *)
      remember (zkpPermutationCommitment grp (List.length cand_all)
                                         pi cpi s) as zkpcpi. 
      (* At this point I can assert that 
         verify_permutation_commitment grp (List.length cand_all) cpi zkpcpi = true 
         using the Axiom permutation_commitment_axiom *)
      assert (verify_permutation_commitment grp (List.length cand_all) cpi zkpcpi = true).
      pose proof (permutation_commitment_axiom
                    grp pi cpi s zkpcpi Heqpi Heqcpis Heqzkpcpi). auto.
      (* Construct each row *)
      remember (map (fun c => uenc c) cand_all) as partialballot. 
      (* construct the orignal ballot because it's needed for zkp construction *)
      remember (map (fun b => map b cand_all) partialballot) as nballot.
      (* construct suffled ballot. for each row do rowshuffle *)
      remember (map (fun b => shuffle grp (List.length cand_all)
                                   (map b cand_all) pi) partialballot) as rowShuffledwithR. 
      remember (map fst rowShuffledwithR) as rowshuffled.
      remember (map snd rowShuffledwithR) as rvalues.
      (* Now I have row shuffled ballot by pi, construct zero knowledge proof *)
      remember (construct_zero_knowledge_proof
                  grp (List.length cand_all)
                  nballot rowshuffled pi cpi s rvalues) as zkppermuv.
      
      (* Now convert the rowshuffled ballot into function closure *)
      assert (List.length (List.concat rowshuffled) = List.length (all_pairs_row cand_all)).
      rewrite Heqrowshuffled. rewrite <- (flat_map_concat_map _ rowShuffledwithR).
      rewrite HeqrowShuffledwithR. rewrite Heqpartialballot.
      rewrite (map_map _ _ cand_all).
      rewrite length_all_pairs_row.
      pose proof (flat_map_with_map_row cand_all cand_all uenc grp pi). auto.
      (* Finally, I am feeling good :) *)
      (* Construct function closure v from rowshuffled list *)
      remember (fun (c d : cand) =>
                  match (idx_search _ c d
                                    (all_pairs_row cand_all)(* This would generate in row order *)
                                    (List.concat rowshuffled) (* concat each row *)
                                    (every_cand_row c d) H15) with
                  | existT _  f _ => f
                  end) as v.
      (* Show that verify_row_permutation_ballot uenc v cpi zkppermuv return true.
         The property here is construct matrix from u and v and comp
         This is bit tricky so I am leaving it for the moment because we need to 
         massage the axioms *)
      assert (Ht1 : verify_row_permutation_ballot uenc v cpi zkppermuv = true). admit.
      (* Now I have rowshuffled ballot in form of function closure, 
         Now apply column shuffle on this ballot. Change the name of 
         row_shuffle to shuffle to avoid the confusion*)
      (* Construct the normal ballot in column form for zero knowledge proof construction *)
      remember (map (fun c => map (fun d => v d c) cand_all) cand_all) as colballot.
      remember (map (fun c =>
                       shuffle grp
                               (List.length cand_all)
                               (map (fun d => v d c) cand_all) pi) cand_all) as colShufflewithR.
      remember (map fst colShufflewithR) as colShuffledballot.
      remember (map snd colShufflewithR) as rcolvalues.
      remember (construct_zero_knowledge_proof
                  grp (List.length cand_all)
                  colballot colShuffledballot pi cpi s rcolvalues) as zkppermvw.
      (* Now consvert colshuffledballot into function closure *)
      (* The problem is that each element of colshuffledballot is column of 
         rowshuffle ballot. I want to change it in function closure without 
         changing the structure of ballot. The idea is write another function 
         similiar to all_pairs but produce results in column form. 
         Let's say [A, B, C] => all_pairs would produce
         [AA, AB, AB, BA, BB, BC, CA, CB, CC] so it would kind of mismatch the 
         ballot with idx_search. 
         Write a new function all_pair_col [A, B, C] => 
         [AA, BA,  CA, AB, BB, CB, AC, BC, CC] and call this value with 
         List.concat (colshuffledballot) to make sure that structure presevers. *)
      (* Now I have solved the problem by writing different functions for row and column *)
      
      assert (Datatypes.length (concat colShuffledballot) =
              Datatypes.length (all_pairs_col cand_all)).
      rewrite HeqcolShuffledballot.
      rewrite <- (flat_map_concat_map _ colShufflewithR).
      rewrite HeqcolShufflewithR. rewrite length_all_pairs_col.
      pose proof (flat_map_with_map_col cand_all cand_all v grp pi). auto.            
      remember (fun (c d : cand) =>
                  match (idx_search _ c d
                                    (all_pairs_col cand_all)(* This would generate in col order *)
                                    (List.concat colShuffledballot) (* concat each row *)
                                    (every_cand_col c d) H16) with
                  | existT _  f _ => f
                  end) as w.
      (*  Show that verify_col_permutation_ballot v w cpi zkppermvw return true. 
         This is bit tricky so I am leaving it for the moment because we need to 
         massage the axioms *)
      assert (Ht2 : verify_col_permutation_ballot v w cpi zkppermvw = true). admit.

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
      (* At this point we need Axioms which connects the validity of umat to b 
          H11 : proj1_sig (bool_of_sumbool (matrix_ballot_valid_dec umat)) = true <-> 
          to   Heqb : b = (fun c d : cand => decrypt_message grp privatekey (w c d))
         because if there is no cycle in umat then there won't be any cycle in 
         encryption of umat i.e. uenc => (row shuffle by pi) => v => (column shuffle by pi) =>
         w => (decryption) => b *)
      assert (matrix_ballot_valid b).  admit.
      specialize (X uenc v w b zkppermuv zkppermvw zkpdecw cpi
                    zkpcpi ets
                    (fun c d : cand => encrypt_message grp (m c d))
                    (fun c d : cand => homomorphic_addition
                                      grp (uenc c d)
                                      (encrypt_message grp (m c d)))
                    etinbs IHCount H17 H14 Ht1 Ht2 Ht3).
      simpl in X.
      assert ((forall c d : cand,
                  homomorphic_addition grp (uenc c d) (encrypt_message grp (m c d)) =
                  homomorphic_addition grp (uenc c d) (encrypt_message grp (m c d)))).
      intros. auto.
      specialize (X H18).
      (*  ECount grp ebs
        (epartial (ets, etinbs)
           (fun c d : cand => homomorphic_addition grp (uenc c d) (encrypt_message grp (m c d)))) *)
      
      assert (em = (fun c d : cand => homomorphic_addition
                                     grp (uenc c d) (encrypt_message grp (m c d)))).
      apply functional_extensionality. intros.
      apply functional_extensionality. intros. 
      pose proof (homomorphic_addition_axiom grp x x0 uenc
                                             (fun c d => encrypt_message grp (m c d))).
      simpl in H19. rewrite decryption_deterministic in H19. 
      rewrite Hequenc in H19. rewrite decryption_deterministic in H19. (* Admit it for the moment *)
      admit. rewrite H19. assumption.

      (* Now we are in situation where u is not valid and this correspondence should reflect on 
         the validity of matrix contructed from u *)
      (*  H : Count bs (partial (u :: us, inbs) m)
          e : exists c : cand, u c = 0%nat *)
  
      intros. inversion H0.
      (* Change u to matrix form umat *)
       remember (fun c d =>
                  if (u c <? u d)%nat &&  (0 <? u c )%nat then 1 
                  else if (u c =? u d)%nat && (0 <? u c)%nat then  0
                       else  if (u d <? u c)%nat && (0 <? u d)%nat then 0
                             else -1) as umat.
      (* Show that they are equivalent *)
      pose proof (connect_validity_of_ballot_pballot u umat).
      assert (forall c d : cand, map_ballot_pballot u umat c d = true).
      intros c d. unfold map_ballot_pballot.
      remember (umat c d) as tumat.
      rewrite Hequmat in Heqtumat.
      destruct ((u c <? u d)%nat && (0 <? u c)%nat) in *.
      apply Z.eqb_eq in Heqtumat. auto.
      destruct ((u c =? u d)%nat && (0 <? u c)%nat).
      apply Z.eqb_eq in Heqtumat. auto.
      destruct ((u d <? u c)%nat && (0 <? u d)%nat).
      apply Z.eqb_eq in Heqtumat. auto.
      apply Z.eqb_eq in Heqtumat. auto.
      specialize (H6 H10).
      (* valid b <-> valid u *)
      destruct H6 as [H11 H12].
      (* Assert that u is not valid *) 
      assert (proj1_sig (bool_of_sumbool (ballot_valid_dec u)) = false).
      destruct (ballot_valid_dec u); simpl; try auto.
      destruct e as [c Hc]. pose proof (g c). omega.
      (* At this point I know that my ballot u is not valid so umat also won't be valid so 
         don't count it and move to invalid list *)
      pose proof (proj1 (connect_invalidity_of_ballot_pballot _ _ H10) H6).
      (* so u is not valid then umat is also not valid so don't add it. *)
      clear H11. clear H12.  

      assert (forall (A : Type) (l : list A),
                 l <> [] -> existsT t l', l = t :: l').
      intros. destruct l.  intuition.
      exists a, l. auto.
      assert (tinbs <> []). unfold not; intros.
      destruct tinbs. inversion H8. inversion H11.
      destruct (X _ tinbs H11) as [t [tinbs' Hinbs']].
      clear H11.

      rewrite Hinbs' in H5.
      (* now assert etpbs <> [] *)
      assert (etpbs <> []). unfold not; intros.
      rewrite H11 in H5. simpl in H5. inversion H5.
      destruct (X _ etpbs H11) as [et [etpbs' Hetpbs']].
      clear H11.
      (* assert einbs <> [] *)
      assert (etinbs <> []). unfold not; intros.
      rewrite H11 in H3. simpl in H3. rewrite Hetpbs' in H3.
      inversion H3.
      destruct (X _ etinbs H11) as [eti [etinbs' Hetinbs']].
      clear H11.
      rewrite Hinbs' in H8. inversion H8.
      rewrite Hetpbs' in H5. simpl in H5. destruct H5.
      rewrite Hetpbs' in H3. rewrite Hetinbs' in H3. simpl in H3.
      inversion H3.

      specialize (IHCount (u :: us) tinbs'
                          ((fun c d => encrypt_message grp (umat c d)) :: ets) etinbs'
                          (umat :: tpbs) etpbs'
                          (fun c d => encrypt_message grp (m c d))).
      simpl in IHCount.
                          
      assert (umat :: tpbs =
              (fun c d : cand => decrypt_message grp privatekey (encrypt_message grp (umat c d)))
                :: map (fun (x : cand -> cand -> ciphertext) (c d : cand) =>
                          decrypt_message grp privatekey (x c d))
                ets).
      assert (umat = (fun c d : cand => decrypt_message grp privatekey
                                                     (encrypt_message grp (umat c d)))).
      apply functional_extensionality. intros.
      apply functional_extensionality. intros.
      rewrite decryption_deterministic. auto.
      rewrite <- H15. apply f_equal. auto.
      specialize (IHCount H15 H17). clear H15.
      assert ((forall c d : cand, map_ballot_pballot u umat c d = true) /\ mapping_ballot_pballot us tpbs).
      split; try auto.
      rewrite <- H7 in H4. auto.
      specialize (IHCount H15 H11). clear H15.

      assert (m = (fun c d : cand => decrypt_message grp privatekey (encrypt_message grp (m c d)))).
      apply functional_extensionality. intros.
      apply functional_extensionality. intros.
      rewrite decryption_deterministic. auto.
      rewrite <- H15 in IHCount.
      rewrite <- H14 in IHCount.
      specialize (IHCount eq_refl). 
      (* Now I am in state 
          IHCount : ECount grp ebs
              (epartial ((fun c d : cand => encrypt_message grp (umat c d)) :: ets, etinbs')
                 (fun c d : cand => encrypt_message grp (m c d))) 
        From This state I count the ballot umat because it's valid, and move on 
        use ecivalid to proceed *)
      clear H3. clear H8. clear X.

      pose proof (ecinvalid grp ebs).
      remember (fun c d : cand => encrypt_message grp (umat c d)) as uenc.
      (* instantiate u with uenc. *)
      (* This is same as  ppartial_count_all_counted  *)
      (* generate permutation *) 
      remember (generatePermutation grp (List.length cand_all)) as pi.
      (* commit it *)
      remember (generatePermutationCommitment grp (List.length cand_all) pi) as cpis.
      destruct cpis as (cpi, s).
      (* generate zero knowledge proof of commitment *)
      remember (zkpPermutationCommitment grp (List.length cand_all)
                                         pi cpi s) as zkpcpi. 
      (* At this point I can assert that 
         verify_permutation_commitment grp (List.length cand_all) cpi zkpcpi = true 
         using the Axiom permutation_commitment_axiom *)
      assert (verify_permutation_commitment grp (List.length cand_all) cpi zkpcpi = true).
      pose proof (permutation_commitment_axiom
                    grp pi cpi s zkpcpi Heqpi Heqcpis Heqzkpcpi). auto.
      (* Construct each row *)
      remember (map (fun c => uenc c) cand_all) as partialballot. 
      (* construct the orignal ballot because it's needed for zkp construction *)
      remember (map (fun b => map b cand_all) partialballot) as nballot.
      (* construct suffled ballot. for each row do rowshuffle *)
      remember (map (fun b => shuffle grp (List.length cand_all)
                                   (map b cand_all) pi) partialballot) as rowShuffledwithR. 
      remember (map fst rowShuffledwithR) as rowshuffled.
      remember (map snd rowShuffledwithR) as rvalues.
      (* Now I have row shuffled ballot by pi, construct zero knowledge proof *)
      remember (construct_zero_knowledge_proof
                  grp (List.length cand_all)
                  nballot rowshuffled pi cpi s rvalues) as zkppermuv.

      (* Now convert the rowshuffled ballot into function closure *)
      assert (List.length (List.concat rowshuffled) = List.length (all_pairs_row cand_all)).
      rewrite Heqrowshuffled. rewrite <- (flat_map_concat_map _ rowShuffledwithR).
      rewrite HeqrowShuffledwithR. rewrite Heqpartialballot.
      rewrite (map_map _ _ cand_all).
      rewrite length_all_pairs_row.
      pose proof (flat_map_with_map_row cand_all cand_all uenc grp pi). auto.
      (* Finally, I am feeling good :) *)
      (* Construct function closure v from rowshuffled list *)
      remember (fun (c d : cand) =>
                  match (idx_search _ c d
                                    (all_pairs_row cand_all)(* This would generate in row order *)
                                    (List.concat rowshuffled) (* concat each row *)
                                    (every_cand_row c d) H8) with
                  | existT _  f _ => f
                  end) as v.
      (* Show that verify_row_permutation_ballot uenc v cpi zkppermuv return true.
         The property here is construct matrix from u and v and comp
         This is bit tricky so I am leaving it for the moment because we need to  
         massage the axioms *)

      assert (Ht1 : verify_row_permutation_ballot uenc v cpi zkppermuv = true). admit.
      (* Now I have rowshuffled ballot in form of function closure, 
         Now apply column shuffle on this ballot. Change the name of 
         row_shuffle to shuffle to avoid the confusion*)
      (* Construct the normal ballot in column form for zero knowledge proof construction *)
      remember (map (fun c => map (fun d => v d c) cand_all) cand_all) as colballot.
      remember (map (fun c =>
                       shuffle grp
                               (List.length cand_all)
                               (map (fun d => v d c) cand_all) pi) cand_all) as colShufflewithR.
      remember (map fst colShufflewithR) as colShuffledballot.
      remember (map snd colShufflewithR) as rcolvalues.
      remember (construct_zero_knowledge_proof
                  grp (List.length cand_all)
                  colballot colShuffledballot pi cpi s rcolvalues) as zkppermvw.

      (* Now consvert colshuffledballot into function closure *)
      (* The problem is that each element of colshuffledballot is column of 
         rowshuffle ballot. I want to change it in function closure without 
         changing the structure of ballot. The idea is write another function 
         similiar to all_pairs but produce results in column form. 
         Let's say [A, B, C] => all_pairs would produce
         [AA, AB, AB, BA, BB, BC, CA, CB, CC] so it would kind of mismatch the 
         ballot with idx_search. 
         Write a new function all_pair_col [A, B, C] => 
         [AA, BA,  CA, AB, BB, CB, AC, BC, CC] and call this value with 
         List.concat (colshuffledballot) to make sure that structure presevers. *)
      (* Now I have solved the problem by writing different functions for row and column *)
      
      assert (Datatypes.length (concat colShuffledballot) =
              Datatypes.length (all_pairs_col cand_all)).
      rewrite HeqcolShuffledballot.
      rewrite <- (flat_map_concat_map _ colShufflewithR).
      rewrite HeqcolShufflewithR. rewrite length_all_pairs_col.
      pose proof (flat_map_with_map_col cand_all cand_all v grp pi). auto.          
      remember (fun (c d : cand) =>
                  match (idx_search _ c d
                                    (all_pairs_col cand_all)(* This would generate in col order *)
                                    (List.concat colShuffledballot) (* concat each row *)
                                    (every_cand_col c d) H18) with
                  | existT _  f _ => f
                  end) as w.
      
     (*  Show that verify_col_permutation_ballot v w cpi zkppermvw return true. 
         This is bit tricky so I am leaving it for the moment because we need to 
         massage the axioms *)
      assert (Ht2 : verify_col_permutation_ballot v w cpi zkppermvw = true). admit.

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
      (* At this point we need Axioms which connects the validity of umat to b 
          H11 : proj1_sig (bool_of_sumbool (matrix_ballot_valid_dec umat)) = false <-> 
          to   Heqb : b = (fun c d : cand => decrypt_message grp privatekey (w c d))
         because if there is no cycle in umat then there won't be any cycle in 
         encryption of umat i.e. uenc => (row shuffle by pi) => v => (column shuffle by pi) => 
        w => (decryption) => b *)
      assert (~matrix_ballot_valid b). admit.
      specialize (X uenc v w b zkppermuv zkppermvw zkpdecw
                    cpi zkpcpi ets (fun c d : cand => encrypt_message grp (m c d)) etinbs' IHCount
                    H19 H3 Ht1 Ht2 Ht3).
      (*  X : ECount grp ebs (epartial (ets, uenc :: etinbs') 
                         (fun c d : cand => encrypt_message grp (m c d))) *)
      rewrite Hetinbs'.
      (* Now I need to assert eti is same as uenc *)
      (*  uenc = (fun c d : cand => encrypt_message grp (umat c d)) 
          H5 : forall c d : cand, map_ballot_pballot t et c d = true
          H10 : forall c d : cand, map_ballot_pballot u umat c d = true
          H9 : m = (fun c d : cand => decrypt_message grp privatekey (em c d))
          H12 : u = t
          H16 : et = (fun c d : cand => decrypt_message grp privatekey (eti c d)) *)
      assert (umat = et).
      apply functional_extensionality. intros c.
      apply functional_extensionality. intros d.
      intros. pose proof (H5 c d).
      pose proof (H10 c d). rewrite <- H12 in H20.
      unfold map_ballot_pballot in H20.
      unfold map_ballot_pballot in H21.
      destruct ((u c <? u d)%nat && (0 <? u c)%nat).
      apply Z.eqb_eq in H20. apply Z.eqb_eq in  H21.
      rewrite H20. auto.
      destruct ((u c =? u d)%nat && (0 <? u c)%nat).
      apply Z.eqb_eq in H20.
      apply Z.eqb_eq in H21.
      rewrite H20. auto.
      destruct ((u d <? u c)%nat && (0 <? u d)%nat).
      apply Z.eqb_eq in H20.
      apply Z.eqb_eq in H21.
      rewrite H20. auto.
      apply Z.eqb_eq in H20.
      apply Z.eqb_eq in H21.
      rewrite H20. auto.
      (* But there is no way to prove that encryption of umat would be equal to 
         encryption of et because encryption is random *)
      assert (uenc = eti). admit.
      rewrite <- H21.
      assert (em = (fun c d : cand => encrypt_message grp (m c d))).
      apply functional_extensionality. intros c.
      apply functional_extensionality. intros d.
      rewrite H9. (* This is also not provable because if you decrypt em and encrypt it, 
                     you will get something different because encryption is random *)
      admit.
      rewrite H22. assumption.
      (* finished ecinvalid with couple of assumption. Discuss with Dirk *)
      intros.  inversion H0.
    Admitted.
    
      
      

      
    Lemma inc_dec_identity :
      forall grp etpbs, 
       etpbs =
       map
         (fun (x : cand -> cand -> plaintext) (c d : cand) =>
            decrypt_message grp privatekey (encrypt_message grp (x c d))) etpbs.
    Proof.
      intros grp. induction etpbs.
      -- simpl. auto.
      -- simpl.
         --- assert (a =
                     (fun c d : cand => decrypt_message
                                       grp privatekey (encrypt_message grp (a c d)))).
             apply functional_extensionality. intros.
             apply functional_extensionality. intros.
             rewrite decryption_deterministic. auto.
             rewrite <- H. apply f_equal. assumption.
    Qed.
    
    Lemma mat_correspondence :
      forall (inb : list ballot),
        mapping_ballot_pballot
          inb
          (map
             (fun (u : cand -> nat) (c d : cand) =>
                if (u c <? u d)%nat && (0 <? u c)%nat
                then 1
                else
                  if (u c =? u d)%nat && (0 <? u c)%nat
                  then 0
                  else if (u d <? u c)%nat && (0 <? u d)%nat then 0 else -1) inb).
    Proof.
      induction inb. simpl. apply I.
      simpl. split. intros.
      unfold map_ballot_pballot.
      (* It's all manipulation of lemma. Learn ltac once you finish this project *)
    Admitted.
      
       

             
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
      (* destruct (pall_ballots_counted grp ebs) as [einbs [em Hem]]. *)
      pose proof (margin_same_from_both grp bs ebs
                                        pbs H0 H1 _ Hm [] inb []).


      (* At this point, etinbs = convert inb into matrix form and encrypt them , 
         tpbs = [], 
         etpbs = ?,
         em = fun c d => encrypt_message grp (fm c d)
         feeding all the values in X would 
          partial ([], inb) fm =
      partial ([], inb) (fun c d : cand => decrypt_message grp privatekey (em c d))
    => 
       partial ([], inb) fm =
      partial ([], inb) (fun c d : cand => decrypt_message grp privatekey
                 (encrypt_message grp (fm c d))) -> 
            ECount grp ebs (epartial ([], etinbs) (fun c d => encrypt_message grp (fm c d)))
     This is almost done. Try to connect ballots *)

       
      remember (fun (u : cand -> nat) c d =>
                  if (u c <? u d)%nat &&  (0 <? u c )%nat then 1 
                  else if (u c =? u d)%nat && (0 <? u c)%nat then  0
                       else  if (u d <? u c)%nat && (0 <? u d)%nat then 0
                             else -1) as umat. 
      remember (map umat inb) as etpbs.
      remember (map (fun u c d => encrypt_message grp (u c d)) etpbs) as etinbs.
      specialize (X etinbs [] etpbs (fun c d => encrypt_message grp (fm c d)) eq_refl). 
      assert (etpbs =
              map
                (fun (x : cand -> cand -> ciphertext)
                   (c d : cand) => decrypt_message grp privatekey (x c d))
                etinbs).
      rewrite Heqetinbs.
      rewrite map_map.  simpl in X.
      pose proof (inc_dec_identity grp etpbs). assumption.
      specialize (X H I). clear H.
      assert (mapping_ballot_pballot inb etpbs). 
      rewrite Heqetpbs. rewrite Hequmat.
      pose proof (mat_correspondence inb). auto.
      specialize (X H).
      assert (H5 :  fm =
                    (fun c d : cand =>
                       decrypt_message grp privatekey (encrypt_message grp (fm c d)))).
      apply functional_extensionality. intros.
      apply functional_extensionality. intros.
      rewrite decryption_deterministic. auto.
      simpl in X. rewrite <- H5 in X.
      specialize (X eq_refl).

      pose proof (ecdecrypt grp ebs etinbs
                            (fun c d : cand => encrypt_message grp (fm c d))
                            fm
                 (fun c d => construct_zero_knowledge_decryption_proof
                            grp privatekey (encrypt_message grp (fm c d))) X).
      simpl in X0.
      assert (forall c d : cand,
                 verify_zero_knowledge_decryption_proof
                   grp (fm c d) (encrypt_message grp (fm c d))
                   (construct_zero_knowledge_decryption_proof
                      grp privatekey (encrypt_message grp (fm c d))) =
                 true).
      intros. apply verify_true. symmetry.
      rewrite decryption_deterministic. auto.
      specialize (X0 H3). clear H3.
      pose proof (ecfin grp ebs fm (c_wins fm) (wins_loses_type_dec fm) X0
                         (c_wins_true_type fm) (c_wins_false_type fm)).
      pose proof (fin bs fm inb (c_wins fm) (wins_loses_type_dec fm) Hm
                 (c_wins_true_type fm) (c_wins_false_type fm)).
       
      assert (w = c_wins fm).
      apply functional_extensionality. intros.
      
     
      
     
      
     
    


  




   
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

