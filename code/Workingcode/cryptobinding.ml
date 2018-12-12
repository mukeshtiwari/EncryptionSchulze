open Big
open Lib
open Derivation 

let () = Java.init [| "-Djava.class.path=jarfiles/ocaml-java.jar:jarfiles/unicrypt-2.3.jar:jarfiles/jnagmp-2.0.0.jar:jarfiles/jna-4.5.0.jar:jarfiles/schulze.jar:." |]

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

class%java integer "java.lang.Integer" = 
object 
     method int_value : int = "intValue"
     method to_string : string = "toString"
end

(* Java Big integer binding *)
class%java big_integer "java.math.BigInteger" =
object 
        initializer(create : string -> _)
        method to_string : string = "toString"
end

(* binding to prime *)
class%java prime "ch.bfh.unicrypt.helper.prime.Prime" = 
object
       method [@static] get_random_instance : int -> prime = "getRandomInstance"
       method is_safe_prime : bool = "isSafe"
       method to_string : string = "toString" 
end


(* safe_prime binding *)
class%java safe_prime "ch.bfh.unicrypt.helper.prime.SafePrime" =
object
        inherit prime
        method [@static] get_instance : big_integer -> safe_prime = "getInstance"
        method [@static] get_smallest_instance : int -> safe_prime = "getSmallestInstance"
        method to_string : string = "toString"
end

(* cyclic group *)
class%java cyclic_group  "ch.bfh.unicrypt.math.algebra.general.interfaces.CyclicGroup" = object  end
(* Element *)
class%java element "ch.bfh.unicrypt.math.algebra.general.interfaces.Element" = 
object
        method to_string : string = "toString"
        method is_tuple : bool = "isTuple"
        method get_value : 'a Java.obj  = "getValue"
end

class%java set "ch.bfh.unicrypt.math.algebra.general.interfaces.Set" =
object

       method get_random_element : element = "getRandomElement"
       (* method get_element_from_big_int : big_integer -> element = "getElementFrom" *)
       method to_string : string = "toString"
end



class%java tuple "ch.bfh.unicrypt.math.algebra.general.classes.Tuple" = 
object
     inherit element   
     method [@static] get_instance : element -> int -> tuple = "getInstance"
     method get_first : element = "getFirst"    
     method get_last : element = "getLast" 
     method get_at : int -> element = "getAt"
     method add : element -> tuple = "add"
     method get_arity : int = "getArity"
     method to_string : string = "toString"
end

class%java triple "ch.bfh.unicrypt.math.algebra.general.classes.Triple" = 
object 
    inherit tuple
    method [@static] get_instance : element -> element -> element -> triple = "getInstance"
end

class%java pair "ch.bfh.unicrypt.math.algebra.general.classes.Pair" = 
object 
     inherit tuple
     method [@static] construct_pair : element -> element -> pair = "getInstance"
     method get_second : element = "getSecond"
     method to_string : string = "toString"
end

class%java zmod "ch.bfh.unicrypt.math.algebra.dualistic.classes.ZMod" = object end 


class%java zmod_prime "ch.bfh.unicrypt.math.algebra.dualistic.classes.ZModPrime" = 
object
        inherit zmod     
        method to_string : string = "toString"
end

class%java zmod_element "ch.bfh.unicrypt.math.algebra.dualistic.classes.ZModElement" = 
object
       inherit element  (*If I remove this then decryption will not work. In actual file, ZModElement is not subtype of Element, so I have no idea why it's working. *) 
       initializer(get_zmod_element : zmod -> big_integer -> _)
       method to_string : string = "toString"
end

class%java gstar_mod "ch.bfh.unicrypt.math.algebra.multiplicative.classes.GStarMod" = 
object  
        inherit cyclic_group
        method to_string : string = "toString"
end


class%java gstar_mod_prime "ch.bfh.unicrypt.math.algebra.multiplicative.classes.GStarModPrime" = 
object
        inherit gstar_mod
        method get_zmod_order : zmod_prime = "getZModOrder"
        method to_string : string = "toString"
end



class%java gstar_mod_safe_prime "ch.bfh.unicrypt.math.algebra.multiplicative.classes.GStarModSafePrime" =
object
        inherit gstar_mod_prime
        method [@static] get_instance : safe_prime -> gstar_mod_safe_prime = "getInstance"
        method to_string : string = "toString"
end

class%java multiplicative_element "ch.bfh.unicrypt.math.algebra.multiplicative.interfaces.MultiplicativeElement" = 
object 
      inherit element
      method power_element : big_integer -> multiplicative_element = "power"
      method apply_inverse : element -> multiplicative_element = "applyInverse"
      method multiply : element -> multiplicative_element = "multiply"
      method to_string : string = "toString"
end

class%java gstar_mod_element "ch.bfh.unicrypt.math.algebra.multiplicative.classes.GStarModElement" =
object
        inherit multiplicative_element
        initializer(get_element : gstar_mod -> big_integer -> _)
        method to_string : string = "toString"
end

class%java reencryption_scheme "ch.bfh.unicrypt.crypto.schemes.encryption.interfaces.ReEncryptionScheme" = 
object 
      method to_string : string = "toString"
end


class%java elgamal_encryption_scheme "ch.bfh.unicrypt.crypto.schemes.encryption.classes.ElGamalEncryptionScheme" = 
object
        inherit reencryption_scheme
        method [@static] get_scheme : element -> elgamal_encryption_scheme = "getInstance"
        method encrypt_element : element -> element -> element = "encrypt"
        method decrypt_element : element -> element -> element = "decrypt"
        method to_string : string = "toString"
end



class%java generator_function "ch.bfh.unicrypt.math.function.classes.GeneratorFunction" = 
object 
        method [@static] get_instance : element -> generator_function = "getInstance"
        method to_string : string = "toString"
end

class%java permutation "ch.bfh.unicrypt.helper.math.Permutation" = 
object 
       inherit element 
       method [@static] get_instance : int array -> permutation = "getInstance"
       method to_string : string = "toString"
end

class%java permutation_element "ch.bfh.unicrypt.math.algebra.general.classes.PermutationElement" = 
object 
        
        inherit element
        method [@static] get_instance : permutation -> permutation_element = "getInstance" 
        method to_string : string = "toString"
end


class%java  permutation_group "ch.bfh.unicrypt.math.algebra.general.classes.PermutationGroup" =
object
        inherit set  
        method to_string : string = "toString"
end


class%java mixer "ch.bfh.unicrypt.crypto.mixer.interfaces.Mixer" =
object
       
       method get_permutation_group : permutation_group = "getPermutationGroup"
       method generate_randomizations : tuple = "generateRandomizations"
       method shuffle : tuple -> permutation_element -> tuple -> tuple = "shuffle"
       method to_string : string = "toString"
end


class%java reencryption_mixer "ch.bfh.unicrypt.crypto.mixer.classes.ReEncryptionMixer" = 
object
        inherit mixer  
        method [@static] get_instance : reencryption_scheme -> element -> int -> reencryption_mixer = "getInstance"
        method to_string : string = "toString"
end

class%java randomization_commitment_scheme "ch.bfh.unicrypt.crypto.schemes.commitment.interfaces.RandomizedCommitmentScheme" =
object 
        method get_randomization_space : set = "getRandomizationSpace"
        method commit : element -> element -> element = "commit"
end

class%java permutation_commitment_scheme "ch.bfh.unicrypt.crypto.schemes.commitment.classes.PermutationCommitmentScheme" = 
object 
        inherit randomization_commitment_scheme
        method [@static] get_instance : cyclic_group -> int -> permutation_commitment_scheme = "getInstance"
        method to_string : string = "toString"
end

class%java proof_system "ch.bfh.unicrypt.crypto.proofsystem.interfaces.ProofSystem" = 
object 
      method generate : element -> element -> element = "generate"
      method verify : element -> element -> bool = "verify"
      method to_string : string = "toString"
end 

class%java permutation_commitment_proof_system "ch.bfh.unicrypt.crypto.proofsystem.classes.PermutationCommitmentProofSystem" = 
object 
        inherit proof_system
        method [@static] get_instance : cyclic_group -> int -> permutation_commitment_proof_system = "getInstance"
        method to_string : string = "toString"
end

class%java reencryption_shuffle_proof_system "ch.bfh.unicrypt.crypto.proofsystem.classes.ReEncryptionShuffleProofSystem" = 
object
        inherit proof_system 
        method [@static] get_instance : int -> elgamal_encryption_scheme -> element -> reencryption_shuffle_proof_system = "getInstance"
        method to_string : string = "toString"
end

class%java equality_preimage_proof_system "ch.bfh.unicrypt.crypto.proofsystem.classes.EqualityPreimageProofSystem" =
object
        inherit proof_system
        method to_string : string = "toString"
end

class%java schulze_proof_system "schulze.CryptoWrapper" =
object
        (* this function takes Arbitrary Number of Arguments so find a way to pass arguments from Ocaml to java. *)
        (* Work around is once java file which contains function that take arbitrary arugments *)
        method [@static] get_instance : generator_function  ->  generator_function -> equality_preimage_proof_system = "getInstance"
        method [@static] discrete_log : gstar_mod_element -> element -> big_integer = "dLog"
        method [@static] get_empty_tuple : tuple = "constructEmptyTuple"
        method [@static] array_from_permutation_element : permutation_element -> int array = "convertPermtoIntArray"
        method [@static] permutation_element_from_array : int array -> permutation_element = "convertIntArraytoPerm"
        method to_string : string = "toString"
end

(* Write small functions to construct these objects, so that subtyping is explicit and don't expose class binding*)
(* construct big integer from string *)
let big_int_from_string (s : string) : 'a Big_integer.t' = 
   Big_integer.create s


(* take big-integer and returns the object of safe-prime *)
let safe_prime (p : 'a Big_integer.t') = 
    Safe_prime.get_instance p 

(* Construct a group from safe_prime *)
let group_from_safe_prime (p : 'a Safe_prime.t') = 
    Gstar_mod_safe_prime.get_instance p

(* Construct generator data structure. Use this function to construct GStarModElement or Element *)
let generator_from_group grp gen = 
    Gstar_mod_element.get_element grp gen 

(* Elgamal encryption scheme object *)
let elgamal_encryption_scheme_from_generator gen = 
    Elgamal_encryption_scheme.get_scheme gen

(* This function is exist because we have already generated prime, grp, privatekey, and publickey using some 
   external tool. Now we need to convert them into Java data structure passed through OCaml. This function takes 
   publickey as big_integer and returns Java object *)
let generate_public_key grp publickey = 
    Gstar_mod_element.get_element grp publickey 
    
(* Use this function to generate elements of a group *)
let generate_element_of_group grp element = 
     Gstar_mod_element.get_element grp element

(* this function take grp and privatekey and returns java data strucutre for privatekey *)
let get_zmod_prime grp privatekey = 
    let zmodp = Gstar_mod_prime.get_zmod_order grp in
    Zmod_element.get_zmod_element zmodp privatekey

(* compute g ^ x mod p  *)
let compute_power gen msg = 
    Multiplicative_element.power_element gen msg

(* encryption function which takes grp, generator, publickey and msg, and returns 
   encrypted message as Pair of element *)
let encrypt_message_binding grp gen publickey msg = 
    let elgamal = elgamal_encryption_scheme_from_generator gen in
    let pmsg = compute_power gen msg in
    let p =  Pair.of_obj (Elgamal_encryption_scheme.encrypt_element elgamal publickey pmsg) in
    let first = Big_integer.of_obj (Element.get_value (Tuple.get_first p))  in
    let second = Big_integer.of_obj (Element.get_value (Tuple.get_last p)) in 
    (first, second)

(* decryption of encrypted message *)
let decrypt_message_binding grp gen privatekey (first, second) = 
   let elgamal = elgamal_encryption_scheme_from_generator gen in 
   let first_el = generate_element_of_group grp first in
   let second_el = generate_element_of_group grp second in 
   let encmsg = Pair.construct_pair first_el second_el in
   let dec = Elgamal_encryption_scheme.decrypt_element elgamal privatekey encmsg in 
   Schulze_proof_system.discrete_log gen dec 

(* zero knowledge proof construction *)
let construct_encryption_zero_knowledge_proof_binding grp gen publickey privatekey (first, second) = 
   let encoded_message = compute_power gen (decrypt_message_binding grp gen privatekey (first, second)) in 
   let partial_dec = generate_element_of_group grp second in 
   let partial_dec_el = Multiplicative_element.apply_inverse partial_dec encoded_message in 
   let g = Generator_function.get_instance gen in
   let c1 = Generator_function.get_instance (generate_element_of_group grp first) in
   let preimageprf = Schulze_proof_system.get_instance g c1 in 
   let public_input = Pair.construct_pair publickey partial_dec_el in 
   Proof_system.generate preimageprf privatekey public_input

(* zero knowledge proof decryption *)
let verify_decryption_binding grp gen publickey dec_msg (first, second) zkpprf = 
   let encoded_message = compute_power gen dec_msg in 
   let partial_dec = generate_element_of_group grp second in 
   let partial_dec_el = Multiplicative_element.apply_inverse partial_dec encoded_message in 
   let g = Generator_function.get_instance gen in
   let c1 = Generator_function.get_instance (generate_element_of_group grp first) in
   let preimageprf = Schulze_proof_system.get_instance g c1 in 
   let public_input = Pair.construct_pair publickey partial_dec_el in 
   Proof_system.verify preimageprf zkpprf public_input

 
 
(** val generatePermutation : group -> nat -> 'a1 permutation. This function is taken from extracted code. 
    The only difference is here it Java data structure while it's function in OCaml so We need to find a way
    convert this back and forth  **)
let generatePermutation_binding grp gen publickey n =
  let elgamal = elgamal_encryption_scheme_from_generator gen in
  let mix = Reencryption_mixer.get_instance elgamal publickey n in
  let permgrp = Mixer.get_permutation_group mix in 
  Permutation_element.of_obj (Set.get_random_element permgrp)


(** val generateS : group -> nat -> s **)
let generateS_binding grp gen publickey n = 
  let perm_com_scheme = Permutation_commitment_scheme.get_instance grp n in 
  let scm = Randomization_commitment_scheme.get_randomization_space  perm_com_scheme in
  Set.get_random_element scm


(** val generatePermutationCommitment :
    group -> nat -> 'a1 permutation -> s -> commitment. Remember permutation here is function but Java returns 
    list so we need a intermediate functions which takes Java Object and turns it into a function **)
let generatePermutationCommitment_binding grp gen publickey n perm s = 
  let perm_com_scheme = Permutation_commitment_scheme.get_instance grp n in
  Randomization_commitment_scheme.commit perm_com_scheme perm s


(** val zkpPermutationCommitment :
    group -> nat -> 'a1 permutation -> commitment -> s -> zKP **)

let zkpPermutationCommitment_binding grp gen publickey n perm comm s = 
  let pcps = Permutation_commitment_proof_system.get_instance grp n in
  let offline_private_input = Pair.construct_pair perm s in
  let offline_public_input  = comm in 
  Proof_system.generate pcps offline_private_input offline_public_input
  
(* Verify the zkp permutation *) 
let zkpPermutationVerification_binding grp gen publickey n offline_proof offline_public_input = 
  let pcps = Permutation_commitment_proof_system.get_instance grp n in
  Proof_system.verify pcps offline_proof offline_public_input


(** val homomorphic_addition : ciphertext is pair
    group -> ciphertext -> ciphertext -> ciphertext **)
let homomorphic_addition_binding grp gen publickey (c1, d1) (c2, d2) =
  let c1_el = generate_element_of_group grp c1 in 
  let d1_el = generate_element_of_group grp d1 in
  let c2_el = generate_element_of_group grp c2 in     
  let d2_el = generate_element_of_group grp d2 in
  let r1 = Multiplicative_element.multiply c1_el c2_el in
  let r2 = Multiplicative_element.multiply d1_el d2_el in
  (Element.get_value r1, Element.get_value r2) 


(** val generateR : group -> nat -> r **)

let generateR_binding grp gen publickey n = 
  let elgamal = elgamal_encryption_scheme_from_generator gen in
  let mix = Reencryption_mixer.get_instance elgamal publickey n in
  let r = Mixer.generate_randomizations mix in
  r


(** val shuffle :
    group -> nat -> ('a1 -> ciphertext) -> 'a1 permutation -> r -> 'a1 ->
    ciphertext **)
(* Ballot is a function while it's Tuple in Java. map ballot cand_all and it would give you 
   list of ciphertext. Convert it into Java array and pass that java array to unicrypt function 
   which takes java array of ciphertext and prouduces Tuple. 
   The java function would return tuple which needs to converted back in function form. *)
(* not tested yet *)
let shuffle_binding grp gen publickey n ballot perm r =
  let elgamal = elgamal_encryption_scheme_from_generator gen in
  let mix = Reencryption_mixer.get_instance elgamal publickey n in
  let shuffled_ciphertext = Mixer.shuffle mix ballot perm r in
  shuffled_ciphertext



(** val shuffle_zkp :
    group -> nat -> ('a1 -> ciphertext) -> ('a1 -> ciphertext) -> 'a1
    permutation -> commitment -> s -> r -> zKP **)
let shuffle_zkp_binding grp gen publickey n ciphertext shuffled_ciphertext pi cpi s r = 
   let elgamal = elgamal_encryption_scheme_from_generator gen in 
   let reencryption_pf_system = Reencryption_shuffle_proof_system.get_instance n elgamal publickey in 
   let online_private_input = Triple.get_instance pi s r in
   let online_public_input = Triple.get_instance cpi ciphertext shuffled_ciphertext in 
   let online_proof = Proof_system.generate reencryption_pf_system online_private_input online_public_input in
   online_proof


(* verify shuffle proof. *)
let shuffle_zkp_verification_binding grp gen publickey n online_proof online_public_input = 
  let elgamal = elgamal_encryption_scheme_from_generator gen in
  let reencryption_pf_system = Reencryption_shuffle_proof_system.get_instance n elgamal publickey in
  Proof_system.verify reencryption_pf_system online_proof online_public_input


(* construct Java Array from Ocaml list. This function will be needed for changing PermutationElement into list *)
let construct_array_from_permutation_element perm_el = 
   Schulze_proof_system.array_from_permutation_element perm_el

(* construct Ocaml list from Java Array *)
let create_list_from_array arr = 
    let len = Jarray.length arr in 
    let rec loop i acc = 
     if i >= len then (List.rev acc)
     else let v = Jarray.get_int arr i in
          loop (i + 1) (v :: acc) in  loop 0 []

(* Convert OCaml List into Java Array. This will be used to convert permutation function into list -> Java Array -> PermutationElement *)
let construct_array_from_list lst = 
    let len = List.length lst in
    let ballot = Jarray.create_int len in
    let rec loop i = function 
        | [] -> ()
        | h :: tl -> Jarray.set_int ballot i h;
                     loop (i + 1) tl
    in loop 0 lst;
    ballot


(* construct permutation element from array *)
let construct_permutation_element_from_array perm_array = 
   Schulze_proof_system.permutation_element_from_array perm_array

(* ballot from list. It constructs tuple *)
let construct_ballot_from_list grp lst = 
   let empty_tuple =  Schulze_proof_system.get_empty_tuple () in
   let rec loop etuple l = 
        match l with
        | [] -> etuple
        | (c1, c2) :: tl -> 
           let c1_el = generate_element_of_group grp c1 in 
           let c2_el = generate_element_of_group grp c2 in
           let ret_tuple = Tuple.add etuple (Pair.construct_pair c1_el c2_el) in
           loop ret_tuple tl
    in loop empty_tuple lst 

(* convert tuple into pair of list ([(c1, c2) ....]*)
let construct_list_from_ballot tup = 
   let n = Tuple.get_arity tup in 
   let rec loop i acc = 
           if i >= n then (List.rev acc) 
           else 
            let p = Pair.of_obj (Tuple.get_at tup i) in
            let first = Big_integer.of_obj (Element.get_value (Tuple.get_first p)) in
            let second = Big_integer.of_obj (Element.get_value (Tuple.get_last p)) in
            loop (i + 1) ((first, second) :: acc)
   in loop 0 []


(* construct list from function *)
let construct_list_from_function cand_all f = 
    List.map f cand_all

(* construct function from list *)
let construct_function_from_list dec_cand cand_lst lst = 
   fun c -> 
     let rec loop cand_l l = 
         match cand_l, l with 
         | [], _ | _, []  ->  assert false (* absurd case *)
         | d :: cand_t, h :: tl -> 
              if dec_cand c d then h else loop cand_t tl 
     in loop cand_lst lst



(* This is what we need in our implementation. Converts permutation list into permutation function *)
let perm_function cand_list perm_list = 
  let zip_list = List.combine cand_list perm_list in 
  fun c -> List.nth cand_list (List.assoc c zip_list)

let rec list_enum a b = 
  if a >= b then []
  else a :: list_enum (a + 1) b 

(* Converts permutation function into list which will be converted back into java data structure PermutationElement *)
let perm_list cand_all perm_fun = 
  let zip_list = List.combine cand_all (list_enum 0 (List.length cand_all)) in 
  let plist = List.map perm_fun cand_all in
  List.map (fun x -> List.assoc x zip_list) plist   

(* Glue code *)
let construct_group (prime, gen, pubkey) =   
   let safep = safe_prime prime in
   let group = group_from_safe_prime safep in
   let generator = generator_from_group group gen in
   let publickey = generate_public_key group pubkey in   
   (group, generator, publickey)

let construct_private_key (group, generator, publickey) prikey =
   let (grp, gen, pubkey) = construct_group (group, generator, publickey) in
   get_zmod_prime grp prikey

let ocaml_big_int_to_java_big_int pt = 
    big_int_from_string (Big.to_string pt)

let java_big_int_to_ocaml_big_int pt = 
   Big.of_string (Big_integer.to_string pt)  


let encrypt_message (Lib.Group (prime, generator, publickey)) pt = 
  let jpt = ocaml_big_int_to_java_big_int pt in
  let (grp, gen, pubkey) = construct_group (prime, generator, publickey) in 
  let (c1, c2) = encrypt_message_binding grp gen pubkey jpt in 
  (java_big_int_to_ocaml_big_int c1, java_big_int_to_ocaml_big_int c2)


let decrypt_message (Lib.Group (prime, generator, publickey)) privatekey (c1, c2) =
  let (d1, d2) = (ocaml_big_int_to_java_big_int c1, ocaml_big_int_to_java_big_int c2) in
  let (grp, gen, pubkey) = construct_group (prime, generator, publickey) in
  let prikey = construct_private_key (prime, generator, publickey) privatekey in 
  let decmsg = decrypt_message_binding grp gen prikey (d1, d2) in 
  java_big_int_to_ocaml_big_int decmsg
  

let construct_zero_knowledge_decryption_proof (Lib.Group (prime, generator, publickey)) privatekey (c1, c2) =
    let (d1, d2) =  (ocaml_big_int_to_java_big_int c1, ocaml_big_int_to_java_big_int c2) in
    let (grp, gen, pubkey) = construct_group (prime, generator, publickey) in
    let prikey = construct_private_key (prime, generator, publickey) privatekey in
    construct_encryption_zero_knowledge_proof_binding grp gen pubkey prikey (d1, d2)


let verify_zero_knowledge_decryption_proof (Lib.Group (prime, generator, publickey)) pt (c1, c2) zkpprf = 
    let (grp, gen, pubkey) = construct_group (prime, generator, publickey) in
    let jpt = ocaml_big_int_to_java_big_int pt in
    let (d1, d2) =  (ocaml_big_int_to_java_big_int c1, ocaml_big_int_to_java_big_int c2) in
    verify_decryption_binding grp gen pubkey jpt (d1, d2) zkpprf
 

let rec nat_to_int = function 
  | O -> 0
  | S n' -> 1 + nat_to_int n'


let generatePermutation (Lib.Group (prime, generator, publickey)) n cand_list =
  let (grp, gen, pubkey) = construct_group (prime, generator, publickey) in  
  let perm = generatePermutation_binding grp gen pubkey (nat_to_int n) in
  let parr = construct_array_from_permutation_element perm in
  let plist = create_list_from_array parr in
  (* print_list string_of_int plist;
  print_newline (); *)
  Lib.ExistT (perm_function cand_list plist, __) 

let generateS (Lib.Group (prime, generator, publickey)) n =
  let (grp, gen, pubkey) = construct_group (prime, generator, publickey) in
  generateS_binding grp gen pubkey (nat_to_int n)  


let generatePermutationCommitment (Lib.Group (prime, generator, publickey)) n cand_list (Lib.ExistT (f, __)) rands =
  let (grp, gen, pubkey) = construct_group (prime, generator, publickey) in
  let plist = perm_list cand_list f in 
  let parr = construct_array_from_list plist in 
  let perm = construct_permutation_element_from_array parr in    
  generatePermutationCommitment_binding grp gen pubkey (nat_to_int n) perm rands


let zkpPermutationCommitment (Lib.Group (prime, generator, publickey)) n cand_list (Lib.ExistT (f, __)) pcommit rands = 
  let (grp, gen, pubkey) = construct_group (prime, generator, publickey) in
  let plist = perm_list cand_list f in 
  let parr = construct_array_from_list plist in
  let perm = construct_permutation_element_from_array parr in
  zkpPermutationCommitment_binding grp gen pubkey (nat_to_int n) perm pcommit rands


let verify_permutation_commitment (Lib.Group (prime, generator, publickey)) n perm_zkp pcommit = 
  let (grp, gen, pubkey) = construct_group (prime, generator, publickey) in
  zkpPermutationVerification_binding grp gen pubkey (nat_to_int n) perm_zkp pcommit

let homomorphic_addition (Lib.Group (prime, generator, publickey)) (c1, c2) (d1, d2) = 
  let (c1', c2') =  (ocaml_big_int_to_java_big_int c1, ocaml_big_int_to_java_big_int c2) in
  let (d1', d2') =  (ocaml_big_int_to_java_big_int d1, ocaml_big_int_to_java_big_int d2) in
  let (grp, gen, pubkey) = construct_group (prime, generator, publickey) in
  let (fp, sp) = homomorphic_addition_binding grp gen pubkey (c1', c2') (d1', d2') in
  (java_big_int_to_ocaml_big_int fp, java_big_int_to_ocaml_big_int sp)



let generateR (Lib.Group (prime, generator, publickey)) n = 
  let (grp, gen, pubkey) = construct_group (prime, generator, publickey) in
  generateR_binding grp gen pubkey (nat_to_int n)




let shuffle (Lib.Group (prime, generator, publickey)) n cand_all dec_cand bf (Lib.ExistT (f, __)) rn =
   let (grp, gen, pubkey) = construct_group (prime, generator, publickey) in 
   let blist = List.map (fun (c1, c2) -> (ocaml_big_int_to_java_big_int c1, ocaml_big_int_to_java_big_int c2)) (List.map bf cand_all) in 
   let jballot = construct_ballot_from_list grp blist in
   let plist = construct_array_from_list (perm_list cand_all f) in 
   let perm = construct_permutation_element_from_array  plist in
   let sballot = shuffle_binding grp gen pubkey (nat_to_int n) jballot perm rn in
   let shuffled_ballot = List.map (fun (c1, c2) -> (java_big_int_to_ocaml_big_int c1, java_big_int_to_ocaml_big_int c2)) (construct_list_from_ballot sballot) in
   construct_function_from_list dec_cand cand_all shuffled_ballot 
   


let shuffle_zkp (Lib.Group (prime, generator, publickey)) n cand_all ballot shuffled_ballot (Lib.ExistT (f, __)) pcommit rands rn = 
   let (grp, gen, pubkey) = construct_group (prime, generator, publickey) in
   let blist = List.map (fun (c1, c2) -> (ocaml_big_int_to_java_big_int c1, ocaml_big_int_to_java_big_int c2)) (List.map ballot cand_all) in
   let blist_shuffled = List.map (fun (c1, c2) -> (ocaml_big_int_to_java_big_int c1, ocaml_big_int_to_java_big_int c2)) (List.map shuffled_ballot cand_all) in
   let jballot = construct_ballot_from_list grp blist in 
   let jballot_shuffled = construct_ballot_from_list grp blist_shuffled in
   let plist =  construct_array_from_list (perm_list cand_all f) in 
   let perm = construct_permutation_element_from_array  plist in 
   shuffle_zkp_binding grp gen pubkey (nat_to_int n) jballot jballot_shuffled perm pcommit rands rn


let verify_shuffle (Lib.Group (prime, generator, publickey)) n cand_all ballot shuffled_ballot pcommit shuffle_zkp = 
  let (grp, gen, pubkey) = construct_group (prime, generator, publickey) in
  shuffle_zkp_verification_binding grp gen pubkey (nat_to_int n) shuffle_zkp (Triple.get_instance pcommit ballot shuffled_ballot)


let prime = big_int_from_string  "170141183460469231731687303715884114527"
let generator = big_int_from_string "4"
let publickey = big_int_from_string "49228593607874990954666071614777776087"
let privatekey = big_int_from_string "60245260967214266009141128892124363925"




(* It working *)

let print_pair (c1, c2) = "(" ^ Big.to_string c1 ^ ", " ^ Big.to_string c2 ^ ")"

let print_list f lst =
  let rec print_elements = function
    | [] -> ()
    | h  :: t -> print_string (f h); print_string ";"; print_elements t
  in
  print_string "[";
  print_elements lst;
  print_string "]";;


(* This functions just here for testing purpose *)
let rec int_to_nat n = 
        if n <= 0 then O else S (int_to_nat (n - 1))

let () = 
  let emsg = encrypt_message (Lib.Group (prime, generator, publickey)) (Big.of_string "1") in
  let dmsg = decrypt_message (Lib.Group (prime, generator, publickey)) privatekey emsg in 
  let deczkp = construct_zero_knowledge_decryption_proof (Lib.Group (prime, generator, publickey)) privatekey emsg in 
  let verify = verify_zero_knowledge_decryption_proof (Lib.Group (prime, generator, publickey)) dmsg emsg deczkp in
  print_endline (print_pair emsg);
  print_endline (Big.to_string dmsg);
  print_endline (Element.to_string deczkp);
  print_endline (string_of_bool verify);
  let (Lib.ExistT (f, __)) = generatePermutation (Lib.Group (prime, generator, publickey)) (int_to_nat (List.length Lib.cand_all)) Lib.cand_all in
  let plist = List.map f Lib.cand_all in
  print_endline ""
 

(*
let () = 
   (* construct infrastructure *)
   let (grp, gen, pubkey) = construct_group (prime, generator, publickey) in
   let prikey = construct_private_key (prime, generator, publickey) privatekey in
   (* encrypt message, construct zero knowledge proof, decrypt it, and verify it *)
   let (encm1, encm2) = encrypt_message_binding grp gen pubkey (big_int_from_string "1")  in
   let eqi = construct_encryption_zero_knowledge_proof_binding grp gen pubkey prikey (encm1, encm2) in
   let decm = decrypt_message_binding grp gen prikey (encm1, encm2) in
   let verifydec = verify_decryption_binding grp gen pubkey (*big_int_from_string "2"*) decm (encm1, encm2) eqi in
   (*generate permutation, randomness s, commit to permutation, geenrate zero knowledge proof, verify zero knowledge proof *)
   let perm = generatePermutation_binding grp gen pubkey 4 in
   let rands = generateS_binding grp gen pubkey 4 in 
   let pcommit = generatePermutationCommitment_binding grp gen pubkey 4 perm rands in
   let perm_zkp = zkpPermutationCommitment_binding grp gen pubkey 4 perm pcommit rands in
   let b = zkpPermutationVerification_binding grp gen pubkey 4 perm_zkp pcommit in
   (* use homormorphic addition, construct proof, verify them and decrypt the final value *)
   let (fp, sp)  = homomorphic_addition_binding grp gen pubkey (encm1, encm2) (encm1, encm2) in
   let eqs = construct_encryption_zero_knowledge_proof_binding grp gen pubkey prikey (fp, sp) in 
   let newdec = decrypt_message_binding grp gen prikey (fp, sp) in
   let verifyndec = verify_decryption_binding grp gen pubkey newdec (fp, sp) eqs in
   (* generate R, construct ballot, shuffle the ballot, construct zero knowledge proof, verify shuffle zero knowledge proof *)
   let r = generateR_binding grp gen pubkey 4 in
   let ballot = construct_ballot_from_list grp [(fp, sp); (fp, sp); (fp, sp); (fp, sp)] in
   let shuffled_ballot = shuffle_binding grp gen pubkey 4 ballot perm r in
   let shuffle_zkp = shuffle_zkp_binding grp gen pubkey 4 ballot shuffled_ballot perm pcommit rands r in
   let verify_shuffle = shuffle_zkp_verification_binding grp gen pubkey 4 shuffle_zkp (Triple.get_instance pcommit ballot shuffled_ballot) in
   (* convert ballot into ocaml list *) 
   let ballot_list = construct_list_from_ballot ballot in 
   let ballot_fun = construct_function_from_list (=) [0; 1; 2; 3] ballot_list in
   let ballot_list_from_fun = construct_list_from_function [0; 1; 2; 3] ballot_fun in 
   (* This is for testing behaviour of permtuation function *)
   (* Generate ballot, encrypt it *)
   let pballot = [big_int_from_string "10"; big_int_from_string "11"; big_int_from_string "12"; big_int_from_string "13"] in
   let eballot = List.map (fun x -> encrypt_message_binding grp gen pubkey x) pballot in
   let rn = generateR_binding grp gen pubkey 4 in
   let jballot =  construct_ballot_from_list grp eballot in
   let jshuffled_ballot = shuffle_binding grp gen pubkey 4 jballot perm rn in 
   let jshuffled_zkp = shuffle_zkp_binding grp gen pubkey 4 jballot jshuffled_ballot perm pcommit rands rn in (* use r and it will not check *)
   let jverify_shuffle = shuffle_zkp_verification_binding grp gen pubkey 4 jshuffled_zkp (Triple.get_instance pcommit jballot jshuffled_ballot) in  
   (* Now decrypt the ballot and see how permutation behaves *)
   let olist =  construct_list_from_ballot jshuffled_ballot in 
   let dlist = List.map (fun x -> decrypt_message_binding grp gen prikey x) olist in
   let permel = construct_array_from_permutation_element perm in
   let plist = create_list_from_array  permel in
   let construc_arr = construct_array_from_list plist in
   let permelemen = construct_permutation_element_from_array construc_arr in
   print_endline (Element.to_string permelemen); 
   print_list string_of_int plist;
   print_newline ();
   print_list Big_integer.to_string pballot;
   print_newline ();
   print_list Big_integer.to_string dlist;
   print_newline ();
   print_endline (if jverify_shuffle then "true" else "false");
   print_endline (Gstar_mod_element.to_string pubkey);
   print_endline (Zmod_element.to_string prikey);
   print_endline (print_pair (encm1, encm2));
   print_endline (Element.to_string eqi);
   print_endline (Big_integer.to_string decm); 
   print_endline (if verifydec then "true" else "false");
   print_endline (Element.to_string perm);
   print_endline (Element.to_string rands);
   print_endline (Element.to_string pcommit);
   print_endline (Element.to_string perm_zkp);
   print_endline (if b then "true" else "false");
   print_endline (Tuple.to_string r);
   print_endline (print_pair (fp, sp));
   print_endline (Big_integer.to_string newdec);
   print_endline (if verifyndec then "true" else "false");
   print_endline (Tuple.to_string ballot);
   print_endline (Tuple.to_string shuffled_ballot);
   print_endline (Element.to_string shuffle_zkp);
   print_endline (if verify_shuffle then "true" else "false");
   print_list print_pair ballot_list;
   print_newline ();
   print_list print_pair ballot_list_from_fun;
   print_newline (); *)
