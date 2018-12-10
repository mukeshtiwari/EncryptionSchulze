
type __ = Obj.t

type nat =
| O
| S of nat

type ('a, 'b) sum =
| Inl of 'a
| Inr of 'b

val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val length : 'a1 list -> nat

val app : 'a1 list -> 'a1 list -> 'a1 list

type comparison =
| Eq
| Lt
| Gt

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

type ('a, 'p) sigT =
| ExistT of 'a * 'p



module Pos :
 sig
  val compare_cont : comparison -> Big.big_int -> Big.big_int -> comparison

  val compare : Big.big_int -> Big.big_int -> comparison

  val eq_dec : Big.big_int -> Big.big_int -> bool
 end

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val forallb : ('a1 -> bool) -> 'a1 list -> bool

module Z :
 sig
  val compare : Big.big_int -> Big.big_int -> comparison

  val leb : Big.big_int -> Big.big_int -> bool

  val ltb : Big.big_int -> Big.big_int -> bool

  val max : Big.big_int -> Big.big_int -> Big.big_int

  val min : Big.big_int -> Big.big_int -> Big.big_int

  val eq_dec : Big.big_int -> Big.big_int -> bool
 end

val bool_of_sumbool : bool -> bool

val z_lt_dec : Big.big_int -> Big.big_int -> bool

val z_le_dec : Big.big_int -> Big.big_int -> bool

val z_ge_dec : Big.big_int -> Big.big_int -> bool

val z_lt_ge_dec : Big.big_int -> Big.big_int -> bool

val z_ge_lt_dec : Big.big_int -> Big.big_int -> bool

val z_lt_ge_bool : Big.big_int -> Big.big_int -> bool

val all_pairs : 'a1 list -> ('a1 * 'a1) list

val maxlist : Big.big_int list -> Big.big_int

val max_of_nonempty_list_type :
  'a1 list -> ('a1 -> 'a1 -> bool) -> Big.big_int -> ('a1 -> Big.big_int) ->
  ('a1, __) sigT

type 'a finite = ('a list, __) sigT

val phi_one_helper :
  ('a1 -> 'a1 -> Big.big_int) -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool
  option) -> 'a1 -> 'a1 -> bool

val phi_two_helper :
  ('a1 -> 'a1 -> Big.big_int) -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool
  option) -> 'a1 -> 'a1 -> 'a1 -> bool

val phi_two_inhanced :
  ('a1 -> 'a1 -> Big.big_int) -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool
  option) -> 'a1 -> 'a1 list -> 'a1 -> bool

val phi_one_dec :
  ('a1 -> 'a1 -> Big.big_int) -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool
  option) -> 'a1 -> 'a1 list -> bool

val phi_two_dec :
  ('a1 -> 'a1 -> Big.big_int) -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool
  option) -> 'a1 -> 'a1 list -> 'a1 list -> bool

val phi_decidable :
  ('a1 -> 'a1 -> Big.big_int) -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool
  option) -> 'a1 -> 'a1 list -> bool

val transitive_dec_first_fn :
  ('a1 -> 'a1 -> Big.big_int) -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool
  option) -> 'a1 -> 'a1 -> 'a1 -> bool

val transitive_dec_second_fn :
  ('a1 -> 'a1 -> Big.big_int) -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool
  option) -> 'a1 -> 'a1 -> 'a1 list -> bool

val transitive_dec_third_fn :
  ('a1 -> 'a1 -> Big.big_int) -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool
  option) -> 'a1 -> 'a1 list -> 'a1 list -> bool

val transitive_dec_fourth_fn :
  ('a1 -> 'a1 -> Big.big_int) -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool
  option) -> 'a1 list -> 'a1 list -> 'a1 list -> bool

val transitive_dec_fn :
  ('a1 -> 'a1 -> Big.big_int) -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool
  option) -> 'a1 list -> bool

val vl_or_notvl :
  ('a1 -> 'a1 -> Big.big_int) -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool
  option) -> 'a1 list -> (__, __) sum

val decidable_valid :
  ('a1 -> 'a1 -> Big.big_int) -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool
  option) -> 'a1 finite -> bool

type 'cand pathT =
| UnitT of 'cand * 'cand
| ConsT of 'cand * 'cand * 'cand * 'cand pathT

type 'cand wins_type =
  'cand -> (Big.big_int, 'cand pathT * (('cand * 'cand) -> bool, __) sigT)
  sigT

type 'cand loses_type =
  (Big.big_int, ('cand, 'cand pathT * (('cand * 'cand) -> bool, __) sigT)
  sigT) sigT

val listify :
  'a1 list -> ('a1 -> 'a1 -> Big.big_int) -> (('a1 * 'a1) * Big.big_int) list

val linear_search :
  ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> Big.big_int) -> 'a1 -> 'a1 ->
  (('a1 * 'a1) * Big.big_int) list -> Big.big_int

val mM :
  'a1 list -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> Big.big_int) -> nat ->
  (('a1 * 'a1) * Big.big_int) list

val m :
  'a1 list -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> Big.big_int) -> nat ->
  'a1 -> 'a1 -> Big.big_int

val iterated_marg_patht :
  'a1 list -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> Big.big_int) -> nat ->
  Big.big_int -> 'a1 -> 'a1 -> 'a1 pathT

val c_wins :
  'a1 list -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> Big.big_int) -> 'a1 ->
  bool

val iterated_marg_wins_type :
  'a1 list -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> Big.big_int) -> 'a1 ->
  'a1 wins_type

val exists_fin_reify : ('a1 -> bool) -> 'a1 list -> ('a1, __) sigT

val reify_opponent :
  'a1 list -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> Big.big_int) -> 'a1 ->
  ('a1, __) sigT

val iterated_marg_loses_type :
  'a1 list -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> Big.big_int) -> 'a1 ->
  'a1 loses_type

val wins_loses_type_dec :
  'a1 list -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> Big.big_int) -> 'a1 ->
  ('a1 wins_type, 'a1 loses_type) sum

type plaintext = Big.big_int

type ciphertext = Big.big_int * Big.big_int

type 'cand pballot = 'cand -> 'cand -> plaintext

type 'cand eballot = 'cand -> 'cand -> ciphertext

type prime (* AXIOM TO BE REALIZED *)

type generator (* AXIOM TO BE REALIZED *)

type pubkey (* AXIOM TO BE REALIZED *)

type prikey (* AXIOM TO BE REALIZED *)

type decZkp (* AXIOM TO BE REALIZED *)

val privatekey : prikey

type group =
| Group of prime * generator * pubkey

val encrypt_message : group -> plaintext -> ciphertext

val decrypt_message : group -> prikey -> ciphertext -> plaintext

val construct_zero_knowledge_decryption_proof :
  group -> prikey -> ciphertext -> decZkp

type 'cand permutation = ('cand -> 'cand, __) sigT

type commitment (* AXIOM TO BE REALIZED *)

type permZkp (* AXIOM TO BE REALIZED *)

type s (* AXIOM TO BE REALIZED *)

val generatePermutation : group -> nat -> 'a1 list -> 'a1 permutation

val generateS : group -> nat -> s

val generatePermutationCommitment :
  group -> nat -> 'a1 list -> 'a1 permutation -> s -> commitment

val zkpPermutationCommitment :
  group -> nat -> 'a1 list -> 'a1 permutation -> commitment -> s -> permZkp

val homomorphic_addition : group -> ciphertext -> ciphertext -> ciphertext

type r (* AXIOM TO BE REALIZED *)

type shuffleZkp (* AXIOM TO BE REALIZED *)

val generateR : group -> nat -> r

val shuffle :
  group -> nat -> 'a1 list -> ('a1 -> 'a1 -> bool) -> ('a1 -> ciphertext) ->
  'a1 permutation -> r -> 'a1 -> ciphertext

val shuffle_zkp :
  group -> nat -> 'a1 list -> ('a1 -> ciphertext) -> ('a1 -> ciphertext) ->
  'a1 permutation -> commitment -> s -> r -> shuffleZkp

val pair_cand_dec : ('a1 -> 'a1 -> bool) -> ('a1 * 'a1) -> ('a1 * 'a1) -> bool

val partition_integer : Big.big_int -> bool option option

val finite_gen :
  ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> Big.big_int) -> ('a1 * 'a1) list ->
  ('a1 -> 'a1 -> __ -> bool option, __) sum

val finiteness :
  ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> Big.big_int) -> ('a1 * 'a1) list ->
  ('a1 -> 'a1 -> bool option, __) sum

val dec_pballot : 'a1 list -> ('a1 -> 'a1 -> bool) -> 'a1 pballot -> bool

val pballot_valid_dec :
  'a1 list -> ('a1 -> 'a1 -> bool) -> 'a1 pballot -> bool

val matrix_ballot_valid_dec :
  'a1 list -> ('a1 -> 'a1 -> bool) -> 'a1 pballot -> bool

type 'cand eCount =
| Ecax of 'cand eballot list * ('cand -> 'cand -> ciphertext)
   * ('cand -> 'cand -> plaintext) * ('cand -> 'cand -> decZkp)
| Ecvalid of 'cand eballot * 'cand eballot * 'cand eballot * 'cand pballot
   * ('cand -> shuffleZkp) * ('cand -> shuffleZkp)
   * ('cand -> 'cand -> decZkp) * commitment * permZkp * 'cand eballot list
   * ('cand -> 'cand -> ciphertext) * ('cand -> 'cand -> ciphertext)
   * 'cand eballot list * 'cand eCount
| Ecinvalid of 'cand eballot * 'cand eballot * 'cand eballot * 'cand pballot
   * ('cand -> shuffleZkp) * ('cand -> shuffleZkp)
   * ('cand -> 'cand -> decZkp) * commitment * permZkp * 'cand eballot list
   * ('cand -> 'cand -> ciphertext) * 'cand eballot list * 'cand eCount
| Ecdecrypt of 'cand eballot list * ('cand -> 'cand -> ciphertext)
   * ('cand -> 'cand -> plaintext) * ('cand -> 'cand -> decZkp) * 'cand eCount
| Ecfin of ('cand -> 'cand -> Big.big_int) * ('cand -> bool)
   * ('cand -> ('cand wins_type, 'cand loses_type) sum) * 'cand eCount

val ecount_all_ballot :
  'a1 list -> group -> 'a1 eballot list -> ('a1 -> 'a1 -> ciphertext, 'a1
  eCount) sigT

val idx_search_list :
  ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> 'a2 list -> 'a2

val ppartial_count_all_counted :
  'a1 list -> ('a1 -> 'a1 -> bool) -> group -> 'a1 eballot list -> 'a1
  eballot list -> 'a1 eballot list -> ('a1 -> 'a1 -> ciphertext) -> 'a1
  eCount -> ('a1 eballot list, ('a1 -> 'a1 -> ciphertext, 'a1 eCount) sigT)
  sigT

val pall_ballots_counted :
  'a1 list -> ('a1 -> 'a1 -> bool) -> group -> 'a1 eballot list -> ('a1
  eballot list, ('a1 -> 'a1 -> ciphertext, 'a1 eCount) sigT) sigT

val decrypt_margin :
  'a1 list -> ('a1 -> 'a1 -> bool) -> group -> 'a1 eballot list -> ('a1 ->
  'a1 -> plaintext, 'a1 eCount) sigT

val pschulze_winners :
  'a1 list -> ('a1 -> 'a1 -> bool) -> group -> 'a1 eballot list -> ('a1 ->
  bool, 'a1 eCount) sigT

type cand =
| A
| B
| C

val cand_all : cand list

val cand_eq_dec : cand -> cand -> bool

val eschulze_winners_pf :
  group -> cand eballot list -> (cand -> bool, cand eCount) sigT
