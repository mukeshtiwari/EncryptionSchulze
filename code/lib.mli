
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

val z_ge_dec : Big.big_int -> Big.big_int -> bool

val z_lt_ge_dec : Big.big_int -> Big.big_int -> bool

val z_ge_lt_dec : Big.big_int -> Big.big_int -> bool

val z_lt_ge_bool : Big.big_int -> Big.big_int -> bool

val all_pairs : 'a1 list -> ('a1 * 'a1) list

val maxlist : Big.big_int list -> Big.big_int

val max_of_nonempty_list_type :
  'a1 list -> ('a1 -> 'a1 -> bool) -> Big.big_int -> ('a1 -> Big.big_int) ->
  ('a1, __) sigT

val transitive_dec_first :
  ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 -> 'a1 -> bool

val transitive_dec_second :
  ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 -> 'a1 list ->
  bool

val transitive_dec_third :
  ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> 'a1 list
  -> bool

val transitive_dec_fourth :
  ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> 'a1
  list -> bool

val transitive_dec :
  ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool) -> 'a1 list -> bool

type 'a finite = ('a list, __) sigT

val phi_one_helper : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 -> bool

val phi_two_helper : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 -> 'a1 -> (__, __) sum

val phi_two_inhanced :
  ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> 'a1 -> (__, __) sum

val phi_one_dec : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> bool

val phi_two_dec : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> 'a1 list -> bool

val phi_decidable : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> bool

val vl_or_notvl :
  ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool) -> 'a1 list -> (__, __) sum

val decidable_valid :
  ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool) -> 'a1 finite -> bool

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

type 'cand ballot = 'cand -> 'cand -> plaintext

type 'cand eballot = 'cand -> 'cand -> ciphertext

type pubkey (* AXIOM TO BE REALIZED *)

type prikey (* AXIOM TO BE REALIZED *)

val privatekey : prikey

val publickey : pubkey

val encrypt_zero_margin_with_zkp :
  'a1 list -> pubkey -> 'a1 ballot -> 'a1 eballot * Big.big_int

val decrypt_ballot_with_zkp :
  'a1 list -> prikey -> 'a1 eballot -> 'a1 ballot * Big.big_int

val row_permute_encrypted_ballot :
  'a1 list -> pubkey -> 'a1 eballot -> 'a1 eballot * Big.big_int

val column_permute_encrypted_ballot :
  'a1 list -> pubkey -> 'a1 eballot -> 'a1 eballot * Big.big_int

val homomorphic_add_eballots :
  'a1 list -> ('a1 -> 'a1 -> ciphertext) -> 'a1 eballot -> 'a1 -> 'a1 ->
  ciphertext

type 'cand hCount =
| Ax of 'cand eballot list * ('cand -> 'cand -> ciphertext) * Big.big_int
| Cvalid of 'cand eballot * 'cand eballot * 'cand eballot
   * ('cand -> 'cand -> Big.big_int) * Big.big_int * Big.big_int
   * Big.big_int * 'cand eballot list * ('cand -> 'cand -> ciphertext)
   * ('cand -> 'cand -> ciphertext) * 'cand eballot list * 'cand hCount
| Cinvalid of 'cand eballot * 'cand eballot * 'cand eballot
   * ('cand -> 'cand -> Big.big_int) * Big.big_int * Big.big_int
   * Big.big_int * 'cand eballot list * ('cand -> 'cand -> ciphertext)
   * 'cand eballot list * 'cand hCount
| Cdecrypt of 'cand eballot list * ('cand -> 'cand -> ciphertext)
   * ('cand -> 'cand -> plaintext) * Big.big_int * 'cand hCount
| Fin of ('cand -> 'cand -> Big.big_int) * ('cand -> bool)
   * ('cand -> ('cand wins_type, 'cand loses_type) sum) * 'cand hCount

val ballot_valid_dec : 'a1 list -> ('a1 -> 'a1 -> bool) -> 'a1 ballot -> bool

val partial_count_all_counted :
  'a1 list -> ('a1 -> 'a1 -> bool) -> 'a1 eballot list -> 'a1 eballot list ->
  'a1 eballot list -> ('a1 -> 'a1 -> ciphertext) -> 'a1 hCount -> ('a1
  eballot list, ('a1 -> 'a1 -> ciphertext, 'a1 hCount) sigT) sigT

val all_ballots_counted :
  'a1 list -> ('a1 -> 'a1 -> bool) -> 'a1 eballot list -> ('a1 eballot list,
  ('a1 -> 'a1 -> ciphertext, 'a1 hCount) sigT) sigT

val decrypt_margin :
  'a1 list -> ('a1 -> 'a1 -> bool) -> 'a1 eballot list -> ('a1 -> 'a1 ->
  plaintext, 'a1 hCount) sigT

val schulze_winners :
  'a1 list -> ('a1 -> 'a1 -> bool) -> 'a1 eballot list -> ('a1 -> bool, 'a1
  hCount) sigT

type cand =
| A
| B
| C

val cand_all : cand list

val cand_eq_dec : cand -> cand -> bool

val schulze_winners_pf : cand eballot list -> (cand -> bool, cand hCount) sigT
