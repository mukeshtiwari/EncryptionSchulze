
type ('a, 'p) sigT =
| ExistT of 'a * 'p

type plaintext = Big.big_int

type ciphertext = Big.big_int * Big.big_int

type 'cand eballot = 'cand -> 'cand -> ciphertext

type prime (* AXIOM TO BE REALIZED *)

type generator (* AXIOM TO BE REALIZED *)

type pubkey (* AXIOM TO BE REALIZED *)

type prikey (* AXIOM TO BE REALIZED *)

val prime0 : prime

val gen : generator

val privatekey : prikey

val publickey : pubkey

type group =
| Group of prime * generator * pubkey

val encrypt_message : group -> plaintext -> ciphertext

val construct_zero_knowledge_decryption_proof :
  group -> prikey -> ciphertext -> char list

type 'cand eCount =
| Ecax of 'cand eballot list * ('cand -> 'cand -> ciphertext)
   * ('cand -> 'cand -> plaintext) * ('cand -> 'cand -> char list)

val ecount_all_ballot :
  group -> 'a1 eballot list -> ('a1 -> 'a1 -> ciphertext, 'a1 eCount) sigT

type cand =
| A
| B
| C

val unicrypt_encryption_library_call :
  cand eballot list -> (cand -> cand -> ciphertext, cand eCount) sigT
