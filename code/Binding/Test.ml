let () = Java.init [| "-Djava.class.path=ocaml-java/bin/ocaml-java.jar:javacryptocode/jarfiles/unicrypt-2.3.jar:javacryptocode/jarfiles/jnagmp-2.0.0.jar:javacryptocode/jarfiles/jna-4.5.0.jar:." |]

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

(* Element *)

class%java element "ch.bfh.unicrypt.math.algebra.general.interfaces.Element" = 
object
        method to_string : string = "toString"
        method is_tuple : bool = "isTuple"
end

(* Get Element from BigInteger https://github.com/bfh-evg/unicrypt/blob/master/src/main/java/ch/bfh/unicrypt/math/algebra/general/interfaces/Set.java *)
class%java set "ch.bfh.unicrypt.math.algebra.general.interfaces.Set" = 
object 
      method to_string : string = "toString"
end

(*
class%java tuple "ch.bfh.unicrypt.math.algebra.general.classes.Tuple" = 
object
     
     method [@static] get_instance : element -> int -> tuple = "getInstance"
     method get_first : element = "getFirst"    
     method get_last : element = "getLast" 
     method get_at : int -> element = "getAt"
     method to_string : string = "toString"
end

class%java pair "ch.bfh.unicrypt.math.algebra.general.classes.Pair" = 
object 
     inherit tuple
     method [@static] construct_pair : element -> element -> pair = "getInstance"
     method get_second : element = "getSecond"
     method to_string : string = "toString"
end *)

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

class%java elgamal_encryption_scheme_algorithm "ch.bfh.unicrypt.crypto.schemes.encryption.interfaces.EncryptionScheme" = 
object 
        inherit reencryption_scheme     
        method encrypt_element : element -> element -> element = "encrypt"
        method decrypt_element : element -> element -> element = "decrypt"
        method to_string : string = "toString"
end 

class%java elgamal_encryption_scheme "ch.bfh.unicrypt.crypto.schemes.encryption.classes.ElGamalEncryptionScheme" = 
object
        inherit elgamal_encryption_scheme_algorithm
        method [@static] get_scheme : element -> elgamal_encryption_scheme = "getInstance"
        (*method encrypt_element : element -> element -> pair = "encrypt"
        method decrypt_element : element -> pair -> element = "decrypt" *)
        method to_string : string = "toString"
end



class%java generator_function "ch.bfh.unicrypt.math.function.classes.GeneratorFunction" = 
object 
        method [@static] get_instance : element -> generator_function = "getInstance"
        method to_string : string = "toString"
end

class%java equality_preimage_proof_system "ch.bfh.unicrypt.crypto.proofsystem.classes.EqualityPreimageProofSystem" = 
object 
        (* this function takes Arbitrary Number of Arguments so find a way to pass arguments from Ocaml to java. Currently I am getting class not found *)
        method [@static] get_instance : generator_function  ->  generator_function -> equality_preimage_proof_system = "getInstance"
        method to_string : string = "toString"
end



class%java permutation_element "ch.bfh.unicrypt.math.algebra.general.classes.PermutationElement" = 
object 
        
        method get_random_element : permutation_element = "getRandomElement"
        method to_string : string = "toString"
end


class%java  permutation_group "ch.bfh.unicrypt.math.algebra.general.classes.PermutationGroup" =
object
        inherit permutation_element
        method to_string : string = "toString"
end
(*
class%java abstract_set "ch.bfh.unicrypt.math.algebra.general.abstracts.AbstractSet" = 
object 
      
      method get_random_element : permutation_element = "getRandomElement"
      method to_string : string = "toString"
end *)

class%java mixer "ch.bfh.unicrypt.crypto.mixer.interfaces.Mixer" =
object
       
       method get_permutation_group : permutation_group = "getPermutationGroup"
       method to_string : string = "toString"
end


class%java reencryption_mixer "ch.bfh.unicrypt.crypto.mixer.classes.ReEncryptionMixer" = 
object
        inherit mixer  
        method [@static] get_instance : reencryption_scheme -> element -> int -> reencryption_mixer = "getInstance"
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
let encrypt_message grp gen publickey msg = 
    let elgamal = elgamal_encryption_scheme_from_generator gen in
    let pmsg = compute_power gen msg in
    Elgamal_encryption_scheme_algorithm.encrypt_element elgamal publickey pmsg  

(* decryption of encrypted message *)
let decrypt_message grp gen privatekey encmsg = 
   let elgamal = elgamal_encryption_scheme_from_generator gen in 
   Elgamal_encryption_scheme_algorithm.decrypt_element elgamal privatekey encmsg  


(** val generatePermutation : group -> nat -> 'a1 permutation. This function is taken from extracted code **)
let generatePermutation grp gen publickey n =
  let elgamal = elgamal_encryption_scheme_from_generator gen in
  let mix = Reencryption_mixer.get_instance elgamal publickey n in
  let permgrp = Mixer.get_permutation_group mix in 
  permgrp

(*
let construct_encryption_zero_knowledge_proof grp gen publickey privatekey encmsg = 
   let elgamal = elgamal_encryption_scheme_from_generator gen in
   let dec_msg = decrypt_message grp gen privatekey encmsg in 
   let enc_last = Pair.get_second encmsg in 
   Pair.get_second enc_last *)

let () = 
   let safep = safe_prime (big_int_from_string  "170141183460469231731687303715884114527") in
   let grp = group_from_safe_prime safep in
   let gen = generator_from_group grp (big_int_from_string "4") in 
   let elgamal = elgamal_encryption_scheme_from_generator gen in
   let publickey = generate_public_key grp (big_int_from_string "49228593607874990954666071614777776087") in
   let privatekey = get_zmod_prime grp (big_int_from_string "60245260967214266009141128892124363925") in
   let encm = encrypt_message grp gen publickey (big_int_from_string "1") (*generate_element_of_group grp (big_int_from_string  "5")*) in
   let decm = decrypt_message grp gen privatekey encm in
   let perm = generatePermutation grp gen publickey 4 in
   print_endline (Prime.to_string safep);
   print_endline (Gstar_mod_safe_prime.to_string grp);
   print_endline (Gstar_mod_element.to_string gen);
   print_endline (Elgamal_encryption_scheme.to_string elgamal);
   print_endline (Gstar_mod_element.to_string publickey);
   print_endline (Zmod_element.to_string privatekey);
   print_endline (Element.to_string encm);
   print_endline (Element.to_string decm);
   print_endline (Permutation_element.to_string perm)




