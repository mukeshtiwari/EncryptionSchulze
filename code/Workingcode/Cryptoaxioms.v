Require Import List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Logic.FinFun.
Require Import Coq.Program.Basics.
Open Scope Z.
Notation "'existsT' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'existsT' '/ ' x .. y , '/ ' p ']'") : type_scope.

Module Crypto.

  Variable cand : Type.
  Variable cand_all : list cand.
  Hypothesis cand_fin : forall c: cand, In c cand_all.
  Hypothesis dec_cand : forall n m : cand, {n = m} + {n <> m}.
  Hypothesis cand_not_nil : cand_all <> nil.

  
  (* Plain text *)
  Definition plaintext := Z.
  
  (* Cipher text is pair (c1, c2). Elgamal encryption *)
  Definition ciphertext := (Z * Z)%type.

  (* ballot is plain text value *)
  Definition pballot := cand -> cand -> plaintext.
  
  (* eballot is encrypted value *)
  Definition eballot := cand -> cand -> ciphertext.
  
    
  (* Group Definition in Elgamal *) 
  Variable Prime : Type. 
  Variable Generator : Type.
  Variable Pubkey : Type.
  Variable Prikey : Type.
  Variable DecZkp : Type. (* Honest Decryption Zero knowledge Proof *)  
  
  (* private and public key *)
  Variable prime : Prime.
  Variable gen : Generator.
  Variable privatekey : Prikey.
  Variable publickey : Pubkey.
     
  Inductive Group : Type :=
    group : Prime -> Generator -> Pubkey -> Group.
    
  (* This function encrypts the message *)
  Variable encrypt_message :
    Group ->  plaintext -> ciphertext.

  (* This function decrypts the message *)
  Variable decrypt_message :
    Group -> Prikey -> ciphertext -> plaintext.

  (* Decryption is deterministic *)
  Axiom decryption_deterministic :
    forall (grp : Group) (privatekey : Prikey) (pt : plaintext),
      decrypt_message grp privatekey (encrypt_message grp pt) = pt.
    
  (* This function returns zero knowledge proof of encrypted message (c1, c2) *)
  Variable construct_zero_knowledge_decryption_proof :
    Group -> Prikey -> ciphertext -> DecZkp.

  (* This function verifies the zero knowledge proof of plaintext, m, is honest decryption 
       of ciphertext *)
  Axiom verify_zero_knowledge_decryption_proof :
    Group -> plaintext -> ciphertext -> DecZkp -> bool.
 
  (* Axiom about honest decryption zero knowledge proof *)
  Axiom verify_true :
    forall (grp : Group) (pt : plaintext) (ct : ciphertext) (privatekey : Prikey)
      (H : pt = decrypt_message grp privatekey ct),
      verify_zero_knowledge_decryption_proof
        grp pt ct
        (construct_zero_knowledge_decryption_proof grp privatekey ct) = true.
    
  
 
  (* permutation is Bijective function *)
  Definition Permutation := existsT (pi : cand -> cand), (Bijective pi).
  Variable Commitment : Type. 
  Variable PermZkp : Type. (* Permutation Zero Knowledge Proof. It will replaced Java Data structure *)
  Variable S : Type. 
  
  (* The idea is for each ballot u, we are going to count 
       we generate pi, cpi, and zkpcpi. We call row permute function 
       u and pi and it returns v. Then We call column permutation 
       on v and pi and it returns w. We decryp w as b with zero knowledge
       proof. *)

    (* We call a java function which returns permutation. Basically java function returns 
       array which is converted back to function in OCaml land*)
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
    forall (grp : Group) (pi : Permutation) (cpi : Commitment) (s : S) (zkppermcommit : PermZkp)
      (H1 : cpi = generatePermutationCommitment grp (List.length cand_all) cand_all pi s)
      (H2 : zkppermcommit = zkpPermutationCommitment
                              grp (List.length cand_all) cand_all pi cpi s),
      verify_permutation_commitment grp (List.length cand_all)
                                    cpi zkppermcommit = true.
  
  Variable homomorphic_addition :
    Group -> ciphertext -> ciphertext -> ciphertext.
  
  (* Property of Homomorphic addition *)
  Axiom homomorphic_addition_axiom :
    forall (grp : Group) (c d : ciphertext),
      decrypt_message grp privatekey (homomorphic_addition grp c d) =
      decrypt_message grp privatekey c + decrypt_message grp privatekey d.    
  
  
  (* Start of Shuffle code *)     
  Variable R : Type.
  Variable ShuffleZkp : Type.
  
  (* Generate Randomness R separately *)
  Variable generateR : Group -> nat -> R. (* Group and length *) 
  
  (* We need List.length cand_all because mixer object is created using 
       elGamal, publickey and n *)
  Variable shuffle :
    Group -> (* group *)
    nat ->
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
  
  (* verify shuffle *)
  Axiom verify_shuffle:
    Group -> (* group *)
    nat -> (* length *)
    list cand ->
    (cand -> ciphertext) -> (* cipertext *)
    (cand -> ciphertext) -> (* shuffled cipertext *)
    Commitment -> (* permutation commitment *)
    ShuffleZkp -> (* zero knowledge proof of shuffle *)
    bool. (* true or false *)
  
  (* Changed data structure *)
  Axiom verify_shuffle_axiom :
    forall (grp : Group) (pi : Permutation) (cpi : Commitment) (s : S)
      (cp shuffledcp : cand -> ciphertext)
      (r : R) (zkprowshuffle : ShuffleZkp)
      (* H0 : s = generateS grp (List.length cand_all) *)
      (H1 : cpi = generatePermutationCommitment grp (List.length cand_all) cand_all pi s)
      (H2 : shuffledcp = shuffle grp (List.length cand_all) cand_all dec_cand cp pi r)
      (H3 : zkprowshuffle = shuffle_zkp grp (List.length cand_all)
                                        cand_all cp shuffledcp pi cpi s r),
      verify_shuffle grp (List.length cand_all)
                     cand_all cp shuffledcp cpi zkprowshuffle = true. 
  
  
  
  (* Shuffle introduce reencryption *)
  Axiom shuffle_perm :
    forall grp n f pi r g, 
      shuffle grp n cand_all dec_cand (f : cand -> ciphertext) (pi : Permutation) r = g ->
      forall c, decrypt_message grp privatekey (g c) =
           decrypt_message grp privatekey (compose f (projT1 pi) c).
  
  (* end of axioms about shuffle. *)    
  

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
      existsT (pi : Permutation), forall (f g : cand -> ciphertext) (zkppf : ShuffleZkp), 
    verify_shuffle grp (Datatypes.length cand_all) cand_all f g cpi zkppf = true ->
    forall c, decrypt_message grp privatekey (g c) =
         decrypt_message grp privatekey (compose f (projT1 pi) c).
  

End Crypto.