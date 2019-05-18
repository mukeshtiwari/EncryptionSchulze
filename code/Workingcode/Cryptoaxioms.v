Require Import List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Logic.FinFun.
Require Import Coq.Program.Basics.
Open Scope Z.
Notation "'existsT' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'existsT' '/ ' x .. y , '/ ' p ']'") : type_scope.

(* This is a duplication of cryptographic axioms from EncryptionSchulze.v. It's duplicated here 
   for readability purpose. 
   Note_to_me : Abstract it into Module and Functor.  *)  

Module Crypto.
 
  Variable cand : Type.
  Variable cand_all : list cand.
  Hypothesis cand_fin : forall c: cand, In c cand_all.
  Hypothesis dec_cand : forall n m : cand, {n = m} + {n <> m}.
  Hypothesis cand_not_nil : cand_all <> nil.
   
  (* Plain text is integer. *)
  Definition plaintext := Z.
  
  (* Ciphertext is abstract type *)
  Variable ciphertext : Type. 
  
  (* ballot is plain text value *)
  Definition pballot := cand -> cand -> plaintext.
    
  (* eballot is encrypted value *)
  Definition eballot := cand -> cand -> ciphertext.
    
  
  (* Group Definition in Elgamal *) 
  Variable Prime : Type. (* Large prime number *)
  Variable Generator : Type. (* Group generator *)
  Variable Pubkey : Type. (* Public key *)
  Variable Prikey : Type. (* Private key *)
  Variable DecZkp : Type. (* Honest Decryption Zero knowledge Proof *)  
  
  (* Group infrastrucutre. large prime, generator, private and public key *)
  Variable prime : Prime.
  Variable gen : Generator.
  Variable privatekey : Prikey.
  Variable publickey : Pubkey. 
  
  (* Relation between Public and Private key. This axiom enforces that 
       publickey and privatekey are generated in pair according to 
       key generation protocol.  *)
  Axiom Keypair : Pubkey -> Prikey -> Prop.
  
  (* Coherence Axiom that states that publickey and privatekey are related *)
  Axiom keypair : Keypair publickey privatekey.
    
  (* Inductive type to construct Group from a given large prime, 
       group generator, and publick key *)
  Inductive Group : Type :=
    group : Prime -> Generator -> Pubkey -> Group.
    
  (* This function encrypts the message. It will be instantiated 
       by Crypto library function. In our case, Unicrypt library functions *)
  Variable encrypt_message :
    Group ->  plaintext -> ciphertext.
    
  (* This function decrypts the message *)
  Variable decrypt_message :
    Group -> Prikey -> ciphertext -> plaintext.
  
  
  (* Construct a instance of group *)
  Let grp := group prime gen publickey.
  
  (* Decryption is left inverse, and we can only decrypt when the keys are 
       related  *)
  Axiom decryption_deterministic :
    forall (pt : plaintext),
      decrypt_message grp privatekey (encrypt_message grp pt) = pt.
  
  (* This function returns zero knowledge proof of encrypted message (c1, c2) *)
  Variable construct_zero_knowledge_decryption_proof :
    Group -> Prikey -> ciphertext -> DecZkp.

  (* This function verifies the zero knowledge proof of plaintext, m, is honest decryption 
       of ciphertext *)
  Axiom verify_zero_knowledge_decryption_proof :
    Group -> plaintext -> ciphertext -> DecZkp -> bool.
  
  (* Coherence axiom about honest decryption zero knowledge proof *)
  Axiom verify_honest_decryption_zkp :
    forall (pt : plaintext) (ct : ciphertext)
      (H : pt = decrypt_message grp privatekey ct),
      verify_zero_knowledge_decryption_proof
        grp pt ct
        (construct_zero_knowledge_decryption_proof grp privatekey ct) = true.
    
 
  (* permutation is Bijective function *)
  Definition Permutation := existsT (pi : cand -> cand), (Bijective pi).
  Variable Commitment : Type. (* Pedersan's commitment for a given permutation *) 
  Variable PermZkp : Type. (* Permutation Zero Knowledge Proof. *)
  Variable S : Type. (* Randomeness added during the commitment computation *)

  (* The idea is for each ballot u, we are going to count 
       we generate pi, cpi, and zkpcpi. We call row permute function 
       u and pi and it returns v. Then We call column permutation 
       on v and pi and it returns w. We decryp w as b with zero knowledge
       proof. *)
  
  (* We call a java function which returns permutation. Basically java function returns 
       array which is converted back to function in OCaml land *)
  Variable generatePermutation :
    Group -> (* group *)
    nat -> (* length  *)
    list cand -> (* cand_all *) 
    Permutation.   
  

  (* Generate randomness used in permutation commitment. 
       Tuple s = pcs.getRandomizeSpace().getrandomElement() *)
  Variable generateS : Group -> nat -> S.
    
  (* Pass the permutation and randomness, it returns commitment. The S used here 
       will be used in zero knowledge proof *)
  Variable generatePermutationCommitment :
    Group -> (* group *)
    nat -> (* length *)
    list cand -> (* cand_all *)
    Permutation -> (* pi *)
    S -> (*randomness *)
    Commitment. (* cpi *)

  (* This function takes Permutation Commitment and S and returns ZKP *)
  Variable zkpPermutationCommitment :
    Group -> (* group *)
    nat -> (* length *)
    list cand -> (* cand_all *)
    Permutation -> (* pi *)
    Commitment -> (* cpi *)
    S -> (* randomness *)
    PermZkp.
  
  Axiom verify_permutation_commitment :
    Group -> (* group *)
    nat -> (* length *)
    Commitment -> (* cpi *)
    PermZkp -> (* zero knowledge proof *)
    bool. (* pcps.verify offlineProof offlinePublicInpu *)
  
  
  Axiom permutation_commitment_axiom :
    forall (pi : Permutation) (cpi : Commitment) (s : S) (zkppermcommit : PermZkp)
      (H1 : cpi = generatePermutationCommitment grp (List.length cand_all) cand_all pi s)
      (H2 : zkppermcommit = zkpPermutationCommitment
                              grp (List.length cand_all) cand_all pi cpi s),
      verify_permutation_commitment grp (List.length cand_all)
                                    cpi zkppermcommit = true.
  
  Variable homomorphic_addition :
    Group -> ciphertext -> ciphertext -> ciphertext.
  
  (* Property of Homomorphic addition *)
  Axiom homomorphic_addition_axiom :
    forall (c d : ciphertext),
      decrypt_message grp privatekey (homomorphic_addition grp c d) =
      decrypt_message grp privatekey c + decrypt_message grp privatekey d.    
  
  
  (* Start of Shuffle code *)     
  Variable R : Type. (* Randomeness needed for shuffling the row/column *)
  Variable ShuffleZkp : Type. (* Zero knowledge proof of Shuffle *)
  
  (* Generate Randomness R by passing group and length of candidate list*)
  Variable generateR : Group -> nat -> R.
  
  (* We need List.length cand_all because mixer object is created using 
       elGamal, publickey and n *)
  Variable shuffle :
    Group -> (* group *)
    nat -> (* Length of list cand *)
    list cand -> (* cand_all because we need to convert function into list *)
    (forall n m : cand, {n = m} + {n <> m}) -> (* This is need because we want to construct the ballot *)
    (cand -> ciphertext) -> (* ciphertext *)
    Permutation -> (* pi *)
    R -> (* Randomness R *)
    (cand -> ciphertext).
  
  (* Construct zero knowledge proof from original and shuffled ballot *)   
  (* Each row of ballot is represented by function *)
  Variable shuffle_zkp :
    Group -> (* group *)
    nat -> (* length *)
    list cand -> (* cand_all *)
    (cand -> ciphertext) -> (* cipertext *)
    (cand -> ciphertext) -> (* shuffle cipertext *)
    Permutation -> (* pi *)
    Commitment -> (* cpi *)
    S -> (* s, permutation commitment randomness *)
    R -> (* r, shuffle randomness *)
    ShuffleZkp. (* zero knowledge proof of shuffle *)
  
  (* verify shuffle. This function checks the claim about a shuffled ciphertext is 
       shuffling of a given ciphertext by a permutation whose commitment is given *)
  Axiom verify_shuffle:
    Group -> (* group *)
    nat -> (* length *)
    list cand ->
    (cand -> ciphertext) -> (* cipertext *)
    (cand -> ciphertext) -> (* shuffled cipertext *)
    Commitment -> (* permutation commitment *)
    ShuffleZkp -> (* zero knowledge proof of shuffle *)
    bool. (* true or false *)
  
  (* Coherence Axiom about shuffle. If every thing is 
       followed according to protocol then verify_shuffle function 
       returns true *)
  Axiom verify_shuffle_axiom :
    forall (pi : Permutation) (cpi : Commitment) (s : S)
      (cp shuffledcp : cand -> ciphertext)
      (r : R) (zkprowshuffle : ShuffleZkp)
      (H1 : cpi = generatePermutationCommitment grp (List.length cand_all) cand_all pi s)
      (H2 : shuffledcp = shuffle grp (List.length cand_all) cand_all dec_cand cp pi r)
      (H3 : zkprowshuffle = shuffle_zkp grp (List.length cand_all)
                                        cand_all cp shuffledcp pi cpi s r),
      verify_shuffle grp (List.length cand_all)
                     cand_all cp shuffledcp cpi zkprowshuffle = true. 
  
  
  
  (* Coherence about shuffle introducing reencryption *)
  Axiom shuffle_perm :
    forall n f pi r g, 
      shuffle grp n cand_all dec_cand (f : cand -> ciphertext) (pi : Permutation) r = g ->
      forall c, decrypt_message grp privatekey (g c) =
           decrypt_message grp privatekey (compose f (projT1 pi) c).
  (* end of axioms about shuffle. *)    
  
  
  (* This axiom states that 
       if verify_zero_knowledge_decryption_proof grp d c zkp = true then 
       d is honest decryption of c *)
  Axiom decryption_from_zkp_proof :
    forall c d zkp, 
      verify_zero_knowledge_decryption_proof grp d c zkp = true -> 
      d = decrypt_message grp privatekey c.
  
  (* Coherence axiom about Permutation *)
  Axiom perm_axiom :
    forall cpi zkpcpi, 
      verify_permutation_commitment grp (Datatypes.length cand_all) cpi zkpcpi = true ->
      existsT (pi : Permutation), forall (f g : cand -> ciphertext) (zkppf : ShuffleZkp), 
    verify_shuffle grp (Datatypes.length cand_all) cand_all f g cpi zkppf = true ->
    forall c, decrypt_message grp privatekey (g c) =
         decrypt_message grp privatekey (compose f (projT1 pi) c).

  (* End of Axioms *)

End Crypto.