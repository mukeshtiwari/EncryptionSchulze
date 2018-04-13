type __ = Obj.t

type bool =
| True
| False

type nat =
| O
| S of nat

type ('a, 'b) sum =
| Inl of 'a
| Inr of 'b

type ('a, 'b) prod =
| Pair of 'a * 'b

val fst : ('a1, 'a2) prod -> 'a1

val snd : ('a1, 'a2) prod -> 'a2

type 'a list =
| Nil
| Cons of 'a * 'a list

val length : 'a1 list -> nat

val app : 'a1 list -> 'a1 list -> 'a1 list

type comparison =
| Eq
| Lt
| Gt

val compOpp : comparison -> comparison

type 'a sig0 =
  'a
  (* singleton inductive, whose constructor was exist *)

type ('a, 'p) sigT =
| ExistT of 'a * 'p

type sumbool =
| Left
| Right

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos :
 sig
  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison

  val eq_dec : positive -> positive -> sumbool
 end

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val forallb : ('a1 -> bool) -> 'a1 list -> bool

module Z :
 sig
  val compare : z -> z -> comparison

  val leb : z -> z -> bool

  val ltb : z -> z -> bool

  val max : z -> z -> z

  val min : z -> z -> z

  val eq_dec : z -> z -> sumbool
 end

val bool_of_sumbool : sumbool -> bool

val z_lt_dec : z -> z -> sumbool

val z_ge_dec : z -> z -> sumbool

val z_lt_ge_dec : z -> z -> sumbool

val z_ge_lt_dec : z -> z -> sumbool

val z_lt_ge_bool : z -> z -> bool

val all_pairs : 'a1 list -> ('a1, 'a1) prod list

val maxlist : z list -> z

val max_of_nonempty_list_type :
  'a1 list -> ('a1 -> 'a1 -> sumbool) -> z -> ('a1 -> z) -> ('a1, __) sigT

val transitive_dec_first :
  ('a1 -> 'a1 -> sumbool) -> ('a1 -> 'a1 -> sumbool) -> 'a1 -> 'a1 -> 'a1 ->
  sumbool

val transitive_dec_second :
  ('a1 -> 'a1 -> sumbool) -> ('a1 -> 'a1 -> sumbool) -> 'a1 -> 'a1 -> 'a1
  list -> sumbool

val transitive_dec_third :
  ('a1 -> 'a1 -> sumbool) -> ('a1 -> 'a1 -> sumbool) -> 'a1 -> 'a1 list ->
  'a1 list -> sumbool

val transitive_dec_fourth :
  ('a1 -> 'a1 -> sumbool) -> ('a1 -> 'a1 -> sumbool) -> 'a1 list -> 'a1 list
  -> 'a1 list -> sumbool

val transitive_dec :
  ('a1 -> 'a1 -> sumbool) -> ('a1 -> 'a1 -> sumbool) -> 'a1 list -> sumbool

type 'a finite = ('a list, __) sigT

val phi_one_helper : ('a1 -> 'a1 -> sumbool) -> 'a1 -> 'a1 -> sumbool

val phi_two_helper :
  ('a1 -> 'a1 -> sumbool) -> 'a1 -> 'a1 -> 'a1 -> (__, __) sum

val phi_two_inhanced :
  ('a1 -> 'a1 -> sumbool) -> 'a1 -> 'a1 list -> 'a1 -> (__, __) sum

val phi_one_dec : ('a1 -> 'a1 -> sumbool) -> 'a1 -> 'a1 list -> sumbool

val phi_two_dec :
  ('a1 -> 'a1 -> sumbool) -> 'a1 -> 'a1 list -> 'a1 list -> sumbool

val phi_decidable : ('a1 -> 'a1 -> sumbool) -> 'a1 -> 'a1 list -> sumbool

val vl_or_notvl :
  ('a1 -> 'a1 -> sumbool) -> ('a1 -> 'a1 -> sumbool) -> 'a1 list -> (__, __)
  sum

val decidable_valid :
  ('a1 -> 'a1 -> sumbool) -> ('a1 -> 'a1 -> sumbool) -> 'a1 finite -> sumbool

type 'cand pathT =
| UnitT of 'cand * 'cand
| ConsT of 'cand * 'cand * 'cand * 'cand pathT

type 'cand wins_type =
  'cand -> (z, ('cand pathT, (('cand, 'cand) prod -> bool, __) sigT) prod)
  sigT

type 'cand loses_type =
  (z, ('cand, ('cand pathT, (('cand, 'cand) prod -> bool, __) sigT) prod)
  sigT) sigT

val listify : 'a1 list -> ('a1 -> 'a1 -> z) -> (('a1, 'a1) prod, z) prod list

val linear_search :
  ('a1 -> 'a1 -> sumbool) -> ('a1 -> 'a1 -> z) -> 'a1 -> 'a1 -> (('a1, 'a1)
  prod, z) prod list -> z

val mM :
  'a1 list -> ('a1 -> 'a1 -> sumbool) -> ('a1 -> 'a1 -> z) -> nat -> (('a1,
  'a1) prod, z) prod list

val m :
  'a1 list -> ('a1 -> 'a1 -> sumbool) -> ('a1 -> 'a1 -> z) -> nat -> 'a1 ->
  'a1 -> z

val iterated_marg_patht :
  'a1 list -> ('a1 -> 'a1 -> sumbool) -> ('a1 -> 'a1 -> z) -> nat -> z -> 'a1
  -> 'a1 -> 'a1 pathT

val c_wins :
  'a1 list -> ('a1 -> 'a1 -> sumbool) -> ('a1 -> 'a1 -> z) -> 'a1 -> bool

val iterated_marg_wins_type :
  'a1 list -> ('a1 -> 'a1 -> sumbool) -> ('a1 -> 'a1 -> z) -> 'a1 -> 'a1
  wins_type

val exists_fin_reify : ('a1 -> sumbool) -> 'a1 list -> ('a1, __) sigT

val reify_opponent :
  'a1 list -> ('a1 -> 'a1 -> sumbool) -> ('a1 -> 'a1 -> z) -> 'a1 -> ('a1,
  __) sigT

val iterated_marg_loses_type :
  'a1 list -> ('a1 -> 'a1 -> sumbool) -> ('a1 -> 'a1 -> z) -> 'a1 -> 'a1
  loses_type

val wins_loses_type_dec :
  'a1 list -> ('a1 -> 'a1 -> sumbool) -> ('a1 -> 'a1 -> z) -> 'a1 -> ('a1
  wins_type, 'a1 loses_type) sum

type plaintext = z

type ciphertext = (z, z) prod

type 'cand ballot = 'cand -> 'cand -> plaintext

type 'cand eballot = 'cand -> 'cand -> ciphertext

type pubkey (* AXIOM TO BE REALIZED *)

type prikey (* AXIOM TO BE REALIZED *)

val privatekey : prikey

val publickey : pubkey

val encrypt_ballot : pubkey -> 'a1 ballot -> 'a1 eballot

val decrypt_ballot : prikey -> 'a1 eballot -> 'a1 ballot

val permute_encrypted_ballot : 'a1 eballot -> ('a1 eballot, z) prod

val homomorphic_add_eballots :
  ('a1 -> 'a1 -> ciphertext) -> 'a1 eballot -> 'a1 -> 'a1 -> ciphertext

type 'cand hCount =
| Ax of 'cand eballot list * ('cand -> 'cand -> ciphertext) * z
| Cvalid of 'cand eballot * 'cand eballot * ('cand -> 'cand -> z) * z * 
   z * 'cand eballot list * ('cand -> 'cand -> ciphertext)
   * ('cand -> 'cand -> ciphertext) * 'cand eballot list * 'cand hCount
| Cinvalid of 'cand eballot * 'cand eballot * ('cand -> 'cand -> z) * 
   z * z * 'cand eballot list * ('cand -> 'cand -> ciphertext)
   * 'cand eballot list * 'cand hCount
| Cdecrypt of 'cand eballot list * ('cand -> 'cand -> ciphertext)
   * ('cand -> 'cand -> plaintext) * z * 'cand hCount
| Fin of ('cand -> 'cand -> z) * ('cand -> bool)
   * ('cand -> ('cand wins_type, 'cand loses_type) sum) * 'cand hCount

val ballot_valid_dec :
  'a1 list -> ('a1 -> 'a1 -> sumbool) -> 'a1 ballot -> sumbool

val partial_count_all_counted :
  'a1 list -> ('a1 -> 'a1 -> sumbool) -> 'a1 eballot list -> 'a1 eballot list
  -> 'a1 eballot list -> ('a1 -> 'a1 -> ciphertext) -> 'a1 hCount -> ('a1
  eballot list, ('a1 -> 'a1 -> ciphertext, 'a1 hCount) sigT) sigT

val all_ballots_counted :
  'a1 list -> ('a1 -> 'a1 -> sumbool) -> 'a1 eballot list -> ('a1 eballot
  list, ('a1 -> 'a1 -> ciphertext, 'a1 hCount) sigT) sigT

val decrypt_margin :
  'a1 list -> ('a1 -> 'a1 -> sumbool) -> 'a1 eballot list -> ('a1 -> 'a1 ->
  plaintext, 'a1 hCount) sigT

val schulze_winners :
  'a1 list -> ('a1 -> 'a1 -> sumbool) -> 'a1 eballot list -> ('a1 -> bool,
  'a1 hCount) sigT

type cand =
| A
| B
| C

val cand_all : cand list

val cand_eq_dec : cand -> cand -> sumbool

val schulze_winners_pf : cand eballot list -> (cand -> bool, cand hCount) sigT
