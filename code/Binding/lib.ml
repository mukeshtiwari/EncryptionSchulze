(* Binding code *)

let () = Java.init [| "-Djava.class.path=ocaml-java/bin/ocaml-java.jar:javacryptocode/jarfiles/unicrypt-2.3.jar:javacryptocode/jarfiles/jnagmp-2.0.0.jar:javacryptocode/jarfiles/jna-4.5.0.jar:schulze.jar:." |]


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

(* end of glue code *)

(*
let prime = big_int_from_string  "170141183460469231731687303715884114527"
let generator = big_int_from_string "4"
let publickey = big_int_from_string "49228593607874990954666071614777776087"
let privatekey = big_int_from_string "60245260967214266009141128892124363925"
*)
(* end of binding *)




(* Extracted code from library *)


type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type nat =
| O
| S of nat

type ('a, 'b) sum =
| Inl of 'a
| Inr of 'b

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

(** val length : 'a1 list -> nat **)

let rec length = function
| [] -> O
| _ :: l' -> S (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m0 =
  match l with
  | [] -> m0
  | a :: l1 -> a :: (app l1 m0)

type comparison =
| Eq
| Lt
| Gt

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

type ('a, 'p) sigT =
| ExistT of 'a * 'p



module Pos =
 struct
  (** val compare_cont :
      comparison -> Big.big_int -> Big.big_int -> comparison **)

  let rec compare_cont = fun c x y -> Big.compare_case c Lt Gt x y

  (** val compare : Big.big_int -> Big.big_int -> comparison **)

  let compare = fun x y -> Big.compare_case Eq Lt Gt x y

  (** val eq_dec : Big.big_int -> Big.big_int -> bool **)

  let rec eq_dec p x0 =
    Big.positive_case
      (fun p0 ->
      Big.positive_case
        (fun p1 -> eq_dec p0 p1)
        (fun _ -> false)
        (fun _ -> false)
        x0)
      (fun p0 ->
      Big.positive_case
        (fun _ -> false)
        (fun p1 -> eq_dec p0 p1)
        (fun _ -> false)
        x0)
      (fun _ ->
      Big.positive_case
        (fun _ -> false)
        (fun _ -> false)
        (fun _ -> true)
        x0)
      p
 end

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: t -> (f a) :: (map f t)

(** val forallb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec forallb f = function
| [] -> true
| a :: l0 -> (&&) (f a) (forallb f l0)

module Z =
 struct
  (** val compare : Big.big_int -> Big.big_int -> comparison **)

  let compare = Big.compare_case Eq Lt Gt

  (** val leb : Big.big_int -> Big.big_int -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val ltb : Big.big_int -> Big.big_int -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false

  (** val max : Big.big_int -> Big.big_int -> Big.big_int **)

  let max = Big.max

  (** val min : Big.big_int -> Big.big_int -> Big.big_int **)

  let min = Big.min

  (** val eq_dec : Big.big_int -> Big.big_int -> bool **)

  let eq_dec x y =
    Big.z_case
      (fun _ ->
      Big.z_case
        (fun _ -> true)
        (fun _ -> false)
        (fun _ -> false)
        y)
      (fun x0 ->
      Big.z_case
        (fun _ -> false)
        (fun p0 -> Pos.eq_dec x0 p0)
        (fun _ -> false)
        y)
      (fun x0 ->
      Big.z_case
        (fun _ -> false)
        (fun _ -> false)
        (fun p0 -> Pos.eq_dec x0 p0)
        y)
      x
 end

(** val bool_of_sumbool : bool -> bool **)

let bool_of_sumbool = function
| true -> true
| false -> false

(** val z_lt_dec : Big.big_int -> Big.big_int -> bool **)

let z_lt_dec x y =
  match Z.compare x y with
  | Lt -> true
  | _ -> false

(** val z_le_dec : Big.big_int -> Big.big_int -> bool **)

let z_le_dec x y =
  match Z.compare x y with
  | Gt -> false
  | _ -> true

(** val z_ge_dec : Big.big_int -> Big.big_int -> bool **)

let z_ge_dec x y =
  match Z.compare x y with
  | Lt -> false
  | _ -> true

(** val z_lt_ge_dec : Big.big_int -> Big.big_int -> bool **)

let z_lt_ge_dec =
  z_lt_dec

(** val z_ge_lt_dec : Big.big_int -> Big.big_int -> bool **)

let z_ge_lt_dec =
  z_ge_dec

(** val z_lt_ge_bool : Big.big_int -> Big.big_int -> bool **)

let z_lt_ge_bool x y =
  bool_of_sumbool (z_lt_ge_dec x y)

(** val all_pairs : 'a1 list -> ('a1 * 'a1) list **)

let rec all_pairs = function
| [] -> []
| c :: cs ->
  (c,
    c) :: (app (all_pairs cs)
            (app (map (fun x -> (c, x)) cs) (map (fun x -> (x, c)) cs)))

(** val maxlist : Big.big_int list -> Big.big_int **)

let rec maxlist = function
| [] -> Big.zero
| h :: t -> (match t with
             | [] -> h
             | _ :: _ -> Z.max h (maxlist t))

(** val max_of_nonempty_list_type :
    'a1 list -> ('a1 -> 'a1 -> bool) -> Big.big_int -> ('a1 -> Big.big_int)
    -> ('a1, __) sigT **)

let max_of_nonempty_list_type l h1 s0 f =
  let rec f0 l0 h2 s1 f1 =
    match l0 with
    | [] -> assert false (* absurd case *)
    | h :: t ->
      (match t with
       | [] -> (fun _ -> ExistT (h, __))
       | h3 :: t1 ->
         let hmax = z_ge_lt_dec (f1 h) (maxlist (map f1 (h3 :: t1))) in
         (fun _ ->
         if hmax
         then ExistT (h, __)
         else let f2 = f0 t h2 s1 f1 __ in
              let ExistT (x, _) = f2 in ExistT (x, __)))
  in f0 l h1 s0 f __

type 'a finite = ('a list, __) sigT

(** val phi_one_helper :
    ('a1 -> 'a1 -> Big.big_int) -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 ->
    bool option) -> 'a1 -> 'a1 -> bool **)

let phi_one_helper _ _ pdec x a =
  let s0 = pdec x a in
  (match s0 with
   | Some s1 ->
     if s1
     then let s2 = pdec a x in (match s2 with
                                | Some _ -> false
                                | None -> true)
     else false
   | None ->
     let s1 = pdec a x in (match s1 with
                           | Some s2 -> s2
                           | None -> false))

(** val phi_two_helper :
    ('a1 -> 'a1 -> Big.big_int) -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 ->
    bool option) -> 'a1 -> 'a1 -> 'a1 -> bool **)

let phi_two_helper _ _ pdec a x a0' =
  let s0 = pdec a x in
  (match s0 with
   | Some s1 ->
     if s1
     then let s2 = pdec a0' x in
          (match s2 with
           | Some s3 ->
             if s3
             then let s4 = pdec x a in
                  (match s4 with
                   | Some s5 ->
                     if s5
                     then let s6 = pdec x a0' in
                          (match s6 with
                           | Some s7 -> s7
                           | None -> false)
                     else let s6 = pdec x a0' in
                          (match s6 with
                           | Some s7 -> if s7 then false else true
                           | None -> false)
                   | None ->
                     let s5 = pdec x a0' in
                     (match s5 with
                      | Some _ -> false
                      | None -> true))
             else false
           | None -> false)
     else let s2 = pdec a0' x in
          (match s2 with
           | Some s3 ->
             if s3
             then false
             else let s4 = pdec x a in
                  (match s4 with
                   | Some s5 ->
                     if s5
                     then let s6 = pdec x a0' in
                          (match s6 with
                           | Some s7 -> s7
                           | None -> false)
                     else let s6 = pdec x a0' in
                          (match s6 with
                           | Some s7 -> if s7 then false else true
                           | None -> false)
                   | None ->
                     let s5 = pdec x a0' in
                     (match s5 with
                      | Some _ -> false
                      | None -> true))
           | None -> false)
   | None ->
     let s1 = pdec a0' x in
     (match s1 with
      | Some _ -> false
      | None ->
        let s2 = pdec x a in
        (match s2 with
         | Some s3 ->
           if s3
           then let s4 = pdec x a0' in
                (match s4 with
                 | Some s5 -> s5
                 | None -> false)
           else let s4 = pdec x a0' in
                (match s4 with
                 | Some s5 -> if s5 then false else true
                 | None -> false)
         | None ->
           let s3 = pdec x a0' in
           (match s3 with
            | Some _ -> false
            | None -> true))))

(** val phi_two_inhanced :
    ('a1 -> 'a1 -> Big.big_int) -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 ->
    bool option) -> 'a1 -> 'a1 list -> 'a1 -> bool **)

let rec phi_two_inhanced p adec pdec a l a0' =
  match l with
  | [] -> true
  | y :: l0 ->
    if phi_two_inhanced p adec pdec a l0 a0'
    then phi_two_helper p adec pdec a y a0'
    else false

(** val phi_one_dec :
    ('a1 -> 'a1 -> Big.big_int) -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 ->
    bool option) -> 'a1 -> 'a1 list -> bool **)

let rec phi_one_dec p adec pdec a = function
| [] -> true
| y :: l0 ->
  if phi_one_dec p adec pdec a l0
  then phi_one_helper p adec pdec y a
  else false

(** val phi_two_dec :
    ('a1 -> 'a1 -> Big.big_int) -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 ->
    bool option) -> 'a1 -> 'a1 list -> 'a1 list -> bool **)

let rec phi_two_dec p adec pdec a l1 l2 =
  match l1 with
  | [] -> false
  | y :: l ->
    if phi_two_dec p adec pdec a l l2
    then true
    else phi_two_inhanced p adec pdec a l2 y

(** val phi_decidable :
    ('a1 -> 'a1 -> Big.big_int) -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 ->
    bool option) -> 'a1 -> 'a1 list -> bool **)

let phi_decidable p adec pdec a l =
  let s0 = phi_two_dec p adec pdec a l l in
  if s0 then true else phi_one_dec p adec pdec a l

(** val transitive_dec_first_fn :
    ('a1 -> 'a1 -> Big.big_int) -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 ->
    bool option) -> 'a1 -> 'a1 -> 'a1 -> bool **)

let transitive_dec_first_fn _ _ pdec c d e =
  let s0 = pdec c d in
  (match s0 with
   | Some s1 ->
     if s1
     then let s2 = pdec d e in
          (match s2 with
           | Some _ ->
             let s3 = pdec c e in
             (match s3 with
              | Some s4 -> s4
              | None -> false)
           | None -> true)
     else let s2 = pdec d e in
          (match s2 with
           | Some s3 ->
             if s3
             then let s4 = pdec c e in
                  (match s4 with
                   | Some s5 -> s5
                   | None -> false)
             else let s4 = pdec c e in
                  (match s4 with
                   | Some s5 -> if s5 then false else true
                   | None -> false)
           | None ->
             let s3 = pdec c e in
             (match s3 with
              | Some _ -> false
              | None -> true))
   | None ->
     let s1 = pdec d e in
     (match s1 with
      | Some s2 ->
        if s2
        then true
        else let s3 = pdec c e in
             (match s3 with
              | Some _ -> false
              | None -> true)
      | None ->
        let s2 = pdec c e in (match s2 with
                              | Some _ -> false
                              | None -> true)))

(** val transitive_dec_second_fn :
    ('a1 -> 'a1 -> Big.big_int) -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 ->
    bool option) -> 'a1 -> 'a1 -> 'a1 list -> bool **)

let rec transitive_dec_second_fn p adec pdec c d = function
| [] -> true
| y :: l0 ->
  if transitive_dec_second_fn p adec pdec c d l0
  then transitive_dec_first_fn p adec pdec c d y
  else false

(** val transitive_dec_third_fn :
    ('a1 -> 'a1 -> Big.big_int) -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 ->
    bool option) -> 'a1 -> 'a1 list -> 'a1 list -> bool **)

let rec transitive_dec_third_fn p adec pdec c l1 l2 =
  match l1 with
  | [] -> true
  | y :: l ->
    if transitive_dec_third_fn p adec pdec c l l2
    then transitive_dec_second_fn p adec pdec c y l2
    else false

(** val transitive_dec_fourth_fn :
    ('a1 -> 'a1 -> Big.big_int) -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 ->
    bool option) -> 'a1 list -> 'a1 list -> 'a1 list -> bool **)

let rec transitive_dec_fourth_fn p adec pdec l1 l2 l3 =
  match l1 with
  | [] -> true
  | y :: l ->
    if transitive_dec_fourth_fn p adec pdec l l2 l3
    then transitive_dec_third_fn p adec pdec y l2 l3
    else false

(** val transitive_dec_fn :
    ('a1 -> 'a1 -> Big.big_int) -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 ->
    bool option) -> 'a1 list -> bool **)

let transitive_dec_fn p adec pdec l =
  transitive_dec_fourth_fn p adec pdec l l l

(** val vl_or_notvl :
    ('a1 -> 'a1 -> Big.big_int) -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 ->
    bool option) -> 'a1 list -> (__, __) sum **)

let rec vl_or_notvl p adec pdec = function
| [] -> Inl __
| y :: l0 ->
  (match vl_or_notvl p adec pdec l0 with
   | Inl _ ->
     let h0 = pdec y y in
     (match h0 with
      | Some s0 ->
        if s0
        then Inr __
        else let h1 = transitive_dec_fn p adec pdec (y :: l0) in
             if h1
             then let h2 = phi_decidable p adec pdec y l0 in
                  if h2 then Inl __ else Inr __
             else Inr __
      | None -> Inr __)
   | Inr _ -> Inr __)

(** val decidable_valid :
    ('a1 -> 'a1 -> Big.big_int) -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 ->
    bool option) -> 'a1 finite -> bool **)

let decidable_valid p adec pdec = function
| ExistT (l, _) ->
  let h0 = vl_or_notvl p adec pdec l in
  (match h0 with
   | Inl _ -> true
   | Inr _ -> false)

type 'cand pathT =
| UnitT of 'cand * 'cand
| ConsT of 'cand * 'cand * 'cand * 'cand pathT

type 'cand wins_type =
  'cand -> (Big.big_int, 'cand pathT * (('cand * 'cand) -> bool, __) sigT)
  sigT

type 'cand loses_type =
  (Big.big_int, ('cand, 'cand pathT * (('cand * 'cand) -> bool, __) sigT)
  sigT) sigT

(** val listify :
    'a1 list -> ('a1 -> 'a1 -> Big.big_int) -> (('a1 * 'a1) * Big.big_int)
    list **)

let listify cand_all0 m0 =
  map (fun s0 -> (((fst s0), (snd s0)), (m0 (fst s0) (snd s0))))
    (all_pairs cand_all0)

(** val linear_search :
    ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> Big.big_int) -> 'a1 -> 'a1 ->
    (('a1 * 'a1) * Big.big_int) list -> Big.big_int **)

let rec linear_search dec_cand marg c d = function
| [] -> marg c d
| y :: t ->
  let (y0, k) = y in
  let (c1, c2) = y0 in
  if dec_cand c c1
  then if dec_cand d c2 then k else linear_search dec_cand marg c d t
  else linear_search dec_cand marg c d t

(** val mM :
    'a1 list -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> Big.big_int) -> nat ->
    (('a1 * 'a1) * Big.big_int) list **)

let rec mM cand_all0 dec_cand marg = function
| O -> listify cand_all0 marg
| S n' ->
  let uu = mM cand_all0 dec_cand marg n' in
  listify cand_all0 (fun c d ->
    let u = linear_search dec_cand marg c d uu in
    let t =
      maxlist
        (map (fun x -> Z.min (marg c x) (linear_search dec_cand marg x d uu))
          cand_all0)
    in
    Z.max u t)

(** val m :
    'a1 list -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> Big.big_int) -> nat ->
    'a1 -> 'a1 -> Big.big_int **)

let m cand_all0 dec_cand marg n =
  let l = mM cand_all0 dec_cand marg n in
  (fun c d -> linear_search dec_cand marg c d l)

(** val iterated_marg_patht :
    'a1 list -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> Big.big_int) -> nat ->
    Big.big_int -> 'a1 -> 'a1 -> 'a1 pathT **)

let rec iterated_marg_patht cand_all0 dec_cand marg n s0 c d =
  match n with
  | O -> UnitT (c, d)
  | S n0 ->
    let c0 =
      Z.compare
        (linear_search dec_cand marg c d (mM cand_all0 dec_cand marg n0))
        (maxlist
          (map (fun x ->
            Z.min (marg c x)
              (linear_search dec_cand marg x d
                (mM cand_all0 dec_cand marg n0))) cand_all0))
    in
    (match c0 with
     | Lt ->
       let h =
         max_of_nonempty_list_type cand_all0 dec_cand s0 (fun x ->
           Z.min (marg c x)
             (linear_search dec_cand marg x d (mM cand_all0 dec_cand marg n0)))
       in
       let ExistT (x, _) = h in
       let iHn = iterated_marg_patht cand_all0 dec_cand marg n0 s0 x d in
       ConsT (c, x, d, iHn)
     | _ -> iterated_marg_patht cand_all0 dec_cand marg n0 s0 c d)

(** val c_wins :
    'a1 list -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> Big.big_int) -> 'a1 ->
    bool **)

let c_wins cand_all0 dec_cand marg c =
  forallb (fun d ->
    Z.leb (m cand_all0 dec_cand marg (length cand_all0) d c)
      (m cand_all0 dec_cand marg (length cand_all0) c d)) cand_all0

(** val iterated_marg_wins_type :
    'a1 list -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> Big.big_int) -> 'a1 ->
    'a1 wins_type **)

let iterated_marg_wins_type cand_all0 dec_cand marg c d =
  let s0 = m cand_all0 dec_cand marg (length cand_all0) c d in
  ExistT (s0,
  (let hi =
     iterated_marg_patht cand_all0 dec_cand marg (length cand_all0) s0 c d
   in
   (hi,
   (let r0 = m cand_all0 dec_cand marg (length cand_all0) d c in
    ExistT ((fun x ->
    Z.leb (m cand_all0 dec_cand marg (length cand_all0) (fst x) (snd x)) r0),
    __)))))

(** val exists_fin_reify : ('a1 -> bool) -> 'a1 list -> ('a1, __) sigT **)

let rec exists_fin_reify pdec = function
| [] -> assert false (* absurd case *)
| h :: t -> if pdec h then ExistT (h, __) else exists_fin_reify pdec t

(** val reify_opponent :
    'a1 list -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> Big.big_int) -> 'a1 ->
    ('a1, __) sigT **)

let reify_opponent cand_all0 dec_cand marg c =
  let hdec = fun d ->
    let s0 =
      z_lt_ge_bool (m cand_all0 dec_cand marg (length cand_all0) c d)
        (m cand_all0 dec_cand marg (length cand_all0) d c)
    in
    if s0 then true else false
  in
  exists_fin_reify hdec cand_all0

(** val iterated_marg_loses_type :
    'a1 list -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> Big.big_int) -> 'a1 ->
    'a1 loses_type **)

let iterated_marg_loses_type cand_all0 dec_cand marg c =
  let hE = reify_opponent cand_all0 dec_cand marg c in
  let ExistT (d, _) = hE in
  let s0 = m cand_all0 dec_cand marg (length cand_all0) d c in
  ExistT (s0, (ExistT (d,
  ((iterated_marg_patht cand_all0 dec_cand marg (length cand_all0) s0 d c),
  (ExistT ((fun x ->
  Z.ltb (m cand_all0 dec_cand marg (length cand_all0) (fst x) (snd x)) s0),
  __))))))

(** val wins_loses_type_dec :
    'a1 list -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> Big.big_int) -> 'a1 ->
    ('a1 wins_type, 'a1 loses_type) sum **)

let wins_loses_type_dec cand_all0 dec_cand marg c =
  let b = c_wins cand_all0 dec_cand marg c in
  if b
  then Inl (iterated_marg_wins_type cand_all0 dec_cand marg c)
  else Inr (iterated_marg_loses_type cand_all0 dec_cand marg c)

type plaintext = Big.big_int

type ciphertext = Big.big_int * Big.big_int

type 'cand pballot = 'cand -> 'cand -> plaintext

type 'cand eballot = 'cand -> 'cand -> ciphertext

type prime =  Big_integer.c Big_integer.t' (* AXIOM TO BE REALIZED *)

type generator =  Big_integer.c Big_integer.t' (* AXIOM TO BE REALIZED *)

type pubkey = Big_integer.c Big_integer.t' (* AXIOM TO BE REALIZED *)

type prikey =  Big_integer.c Big_integer.t' (* AXIOM TO BE REALIZED *)

type decZkp =  string (* AXIOM TO BE REALIZED *)


let prime = big_int_from_string  "170141183460469231731687303715884114527"
let generator = big_int_from_string "4"
let publickey = big_int_from_string "49228593607874990954666071614777776087"
let privatekey = big_int_from_string "60245260967214266009141128892124363925"

(** val privatekey : prikey **)

let privatekey = big_int_from_string "60245260967214266009141128892124363925"

type group =
| Group of prime * generator * pubkey

(** val encrypt_message : group -> plaintext -> ciphertext **)

let encrypt_message (Group (prime, generator, publickey)) pt = 
  let jpt = ocaml_big_int_to_java_big_int pt in
  let (grp, gen, pubkey) = construct_group (prime, generator, publickey) in 
  let (c1, c2) = encrypt_message_binding grp gen pubkey jpt in 
  (java_big_int_to_ocaml_big_int c1, java_big_int_to_ocaml_big_int c2)

(** val decrypt_message : group -> prikey -> ciphertext -> plaintext **)

let decrypt_message (Group (prime, generator, publickey)) privatekey (c1, c2) =
  let (d1, d2) = (ocaml_big_int_to_java_big_int c1, ocaml_big_int_to_java_big_int c2) in
  let (grp, gen, pubkey) = construct_group (prime, generator, publickey) in
  let prikey = construct_private_key (prime, generator, publickey) privatekey in 
  let decmsg = decrypt_message_binding grp gen prikey (d1, d2) in 
  java_big_int_to_ocaml_big_int decmsg
  

(** val construct_zero_knowledge_decryption_proof :
    group -> prikey -> ciphertext -> decZkp **)

let construct_zero_knowledge_decryption_proof (Group (prime, generator, publickey)) privatekey (c1, c2) =
    let (d1, d2) =  (ocaml_big_int_to_java_big_int c1, ocaml_big_int_to_java_big_int c2) in
    let (grp, gen, pubkey) = construct_group (prime, generator, publickey) in
    let prikey = construct_private_key (prime, generator, publickey) privatekey in
    Element.to_string (construct_encryption_zero_knowledge_proof_binding grp gen pubkey prikey (d1, d2)) (* Just for testing purpose this is string. Replace it with Java object *)
  

type 'cand permutation = ('cand -> 'cand, __) sigT

type commitment = Element.t (* AXIOM TO BE REALIZED *)

type permZkp = Element.t (* AXIOM TO BE REALIZED *)

type s = Element.t (* AXIOM TO BE REALIZED *)


let rec nat_to_int = function 
  | O -> 0
  | S n' -> 1 + nat_to_int n'


let print_list f lst =
  let rec print_elements = function
    | [] -> ()
    | h  :: t -> print_string (f h); print_string ";"; print_elements t
  in
  print_string "[";
  print_elements lst;
  print_string "]";;

(** val generatePermutation : group -> nat -> 'a1 list -> 'a1 permutation **)

let generatePermutation (Group (prime, generator, publickey)) n cand_list =
  let (grp, gen, pubkey) = construct_group (prime, generator, publickey) in  
  let perm = generatePermutation_binding grp gen pubkey (nat_to_int n) in
  let parr = construct_array_from_permutation_element perm in
  let plist = create_list_from_array parr in
  print_list string_of_int plist;
  print_newline ();
  ExistT (perm_function cand_list plist, __) 

(** val generateS : group -> nat -> s **)

let generateS (Group (prime, generator, publickey)) n =
  let (grp, gen, pubkey) = construct_group (prime, generator, publickey) in
  generateS_binding grp gen pubkey (nat_to_int n)  

(** val generatePermutationCommitment :
    group -> nat -> 'a1 list -> 'a1 permutation -> s -> commitment **)

let generatePermutationCommitment (Group (prime, generator, publickey)) n cand_list (ExistT (f, __)) rands =
  let (grp, gen, pubkey) = construct_group (prime, generator, publickey) in
  let plist = perm_list cand_list f in 
  let parr = construct_array_from_list plist in 
  let perm = construct_permutation_element_from_array parr in    
  generatePermutationCommitment_binding grp gen pubkey (nat_to_int n) perm rands

(** val zkpPermutationCommitment :
    group -> nat -> 'a1 list -> 'a1 permutation -> commitment -> s -> permZkp **)

let zkpPermutationCommitment (Group (prime, generator, publickey)) n cand_list (ExistT (f, __)) pcommit rands = 
  let (grp, gen, pubkey) = construct_group (prime, generator, publickey) in
  let plist = perm_list cand_list f in 
  let parr = construct_array_from_list plist in
  let perm = construct_permutation_element_from_array parr in
  zkpPermutationCommitment_binding grp gen pubkey (nat_to_int n) perm pcommit rands

(** val homomorphic_addition :
    group -> ciphertext -> ciphertext -> ciphertext **)

let homomorphic_addition (Group (prime, generator, publickey)) (c1, c2) (d1, d2) = 
  let (c1', c2') =  (ocaml_big_int_to_java_big_int c1, ocaml_big_int_to_java_big_int c2) in
  let (d1', d2') =  (ocaml_big_int_to_java_big_int d1, ocaml_big_int_to_java_big_int d2) in
  let (grp, gen, pubkey) = construct_group (prime, generator, publickey) in
  let (fp, sp) = homomorphic_addition_binding grp gen pubkey (c1', c2') (d1', d2') in
  (java_big_int_to_ocaml_big_int fp, java_big_int_to_ocaml_big_int sp)

type r = Tuple.t (* AXIOM TO BE REALIZED *)

type shuffleZkp = Element.t (* AXIOM TO BE REALIZED *)

(** val generateR : group -> nat -> r **)

let generateR (Group (prime, generator, publickey)) n = 
  let (grp, gen, pubkey) = construct_group (prime, generator, publickey) in
  generateR_binding grp gen pubkey (nat_to_int n)


(** val shuffle :
    group -> nat -> 'a1 list -> ('a1 -> 'a1 -> bool) -> ('a1 -> ciphertext)
    -> 'a1 permutation -> r -> 'a1 -> ciphertext **)

let shuffle (Group (prime, generator, publickey)) n cand_all dec_cand bf (ExistT (f, __)) rn =
   let (grp, gen, pubkey) = construct_group (prime, generator, publickey) in 
   let blist = List.map (fun (c1, c2) -> (ocaml_big_int_to_java_big_int c1, ocaml_big_int_to_java_big_int c2)) (List.map bf cand_all) in 
   let jballot = construct_ballot_from_list grp blist in
   let plist = construct_array_from_list (perm_list cand_all f) in 
   let perm = construct_permutation_element_from_array  plist in
   let sballot = shuffle_binding grp gen pubkey (nat_to_int n) jballot perm rn in
   let shuffled_ballot = List.map (fun (c1, c2) -> (java_big_int_to_ocaml_big_int c1, java_big_int_to_ocaml_big_int c2)) (construct_list_from_ballot sballot) in
   construct_function_from_list dec_cand cand_all shuffled_ballot 
   

(** val shuffle_zkp :
    group -> nat -> 'a1 list -> ('a1 -> ciphertext) -> ('a1 -> ciphertext) ->
    'a1 permutation -> commitment -> s -> r -> shuffleZkp **)

let shuffle_zkp (Group (prime, generator, publickey)) n cand_all ballot shuffled_ballot (ExistT (f, __)) pcommit rands rn = 
   let (grp, gen, pubkey) = construct_group (prime, generator, publickey) in
   let blist = List.map (fun (c1, c2) -> (ocaml_big_int_to_java_big_int c1, ocaml_big_int_to_java_big_int c2)) (List.map ballot cand_all) in
   let blist_shuffled = List.map (fun (c1, c2) -> (ocaml_big_int_to_java_big_int c1, ocaml_big_int_to_java_big_int c2)) (List.map shuffled_ballot cand_all) in
   let jballot = construct_ballot_from_list grp blist in 
   let jballot_shuffled = construct_ballot_from_list grp blist_shuffled in
   let plist =  construct_array_from_list (perm_list cand_all f) in 
   let perm = construct_permutation_element_from_array  plist in 
   shuffle_zkp_binding grp gen pubkey (nat_to_int n) jballot jballot_shuffled perm pcommit rands rn

(** val pair_cand_dec :
    ('a1 -> 'a1 -> bool) -> ('a1 * 'a1) -> ('a1 * 'a1) -> bool **)

let pair_cand_dec dec_cand c d =
  let (c0, c1) = c in
  let (c2, c3) = d in
  let h = dec_cand c0 c2 in let h0 = dec_cand c1 c3 in if h then h0 else false

(** val partition_integer : Big.big_int -> bool option option **)

let partition_integer b =
  let s0 = z_le_dec b (Big.opp (Big.double Big.one)) in
  if s0
  then None
  else let s1 = z_ge_dec b (Big.double Big.one) in
       if s1
       then None
       else Some
              (let s2 = Z.eq_dec b (Big.opp Big.one) in
               if s2
               then Some true
               else let s3 = Z.eq_dec b Big.zero in
                    if s3 then Some false else None)

(** val finite_gen :
    ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> Big.big_int) -> ('a1 * 'a1) list
    -> ('a1 -> 'a1 -> __ -> bool option, __) sum **)

let rec finite_gen dec_cand b = function
| [] -> Inl (fun _ _ _ -> assert false (* absurd case *))
| y :: l0 ->
  (match finite_gen dec_cand b l0 with
   | Inl s0 ->
     let (c1, c2) = y in
     let s1 = partition_integer (b c1 c2) in
     (match s1 with
      | Some s2 ->
        Inl (fun c d _ ->
          let s3 = pair_cand_dec dec_cand (c, d) (c1, c2) in
          if s3 then s2 else s0 c d __)
      | None -> Inr __)
   | Inr _ -> Inr __)

(** val finiteness :
    ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> Big.big_int) -> ('a1 * 'a1) list
    -> ('a1 -> 'a1 -> bool option, __) sum **)

let finiteness dec_cand b l =
  let x = finite_gen dec_cand b l in
  (match x with
   | Inl s0 -> Inl (fun c d -> s0 c d __)
   | Inr _ -> Inr __)

(** val dec_pballot :
    'a1 list -> ('a1 -> 'a1 -> bool) -> 'a1 pballot -> bool **)

let dec_pballot cand_all0 dec_cand p =
  let x = finiteness dec_cand p (all_pairs cand_all0) in
  (match x with
   | Inl _ -> true
   | Inr _ -> false)

(** val pballot_valid_dec :
    'a1 list -> ('a1 -> 'a1 -> bool) -> 'a1 pballot -> bool **)

let pballot_valid_dec cand_all0 dec_cand b =
  let x = decidable_valid b dec_cand in
  let ht = finiteness dec_cand b (all_pairs cand_all0) in
  (match ht with
   | Inl s0 -> x s0 (ExistT (cand_all0, __))
   | Inr _ -> false)

(** val matrix_ballot_valid_dec :
    'a1 list -> ('a1 -> 'a1 -> bool) -> 'a1 pballot -> bool **)

let matrix_ballot_valid_dec cand_all0 dec_cand p =
  let s0 = dec_pballot cand_all0 dec_cand p in
  if s0 then pballot_valid_dec cand_all0 dec_cand p else false

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

(** val ecount_all_ballot :
    'a1 list -> group -> 'a1 eballot list -> ('a1 -> 'a1 -> ciphertext, 'a1
    eCount) sigT **)

let ecount_all_ballot _ grp bs =
  let encm = encrypt_message grp Big.zero in
  ExistT ((fun _ _ -> encm), (Ecax (bs, (fun _ _ -> encm), (fun _ _ ->
  Big.zero), (fun _ _ ->
  construct_zero_knowledge_decryption_proof grp privatekey encm))))

(** val idx_search_list :
    ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> 'a2 list -> 'a2 **)

let rec idx_search_list dec_cand c cl l =
  match cl with
  | [] -> assert false (* absurd case *)
  | c0 :: cs ->
    (match l with
     | [] -> assert false (* absurd case *)
     | a :: t -> if dec_cand c c0 then a else idx_search_list dec_cand c cs t)

(** val ppartial_count_all_counted :
    'a1 list -> ('a1 -> 'a1 -> bool) -> group -> 'a1 eballot list -> 'a1
    eballot list -> 'a1 eballot list -> ('a1 -> 'a1 -> ciphertext) -> 'a1
    eCount -> ('a1 eballot list, ('a1 -> 'a1 -> ciphertext, 'a1 eCount) sigT)
    sigT **)

let rec ppartial_count_all_counted cand_all0 dec_cand grp bs ts inbs m0 he =
  match ts with
  | [] -> ExistT (inbs, (ExistT (m0, he)))
  | y :: l ->
    let pi = generatePermutation grp (length cand_all0) cand_all0 in
    let s0 = generateS grp (length cand_all0) in
    let cpi =
      generatePermutationCommitment grp (length cand_all0) cand_all0 pi s0
    in
    let zkpcpi =
      zkpPermutationCommitment grp (length cand_all0) cand_all0 pi cpi s0
    in
    let rrowlistvalues =
      map (fun _ -> generateR grp (length cand_all0)) cand_all0
    in
    let rrowfunvalues = fun c ->
      idx_search_list dec_cand c cand_all0 rrowlistvalues
    in
    let v = fun c ->
      shuffle grp (length cand_all0) cand_all0 dec_cand (y c) pi
        (rrowfunvalues c)
    in
    let zkppermuv = fun c ->
      shuffle_zkp grp (length cand_all0) cand_all0 (y c) (v c) pi cpi s0
        (rrowfunvalues c)
    in
    let rcollistvalues =
      map (fun _ -> generateR grp (length cand_all0)) cand_all0
    in
    let rcolfunvalues = fun c ->
      idx_search_list dec_cand c cand_all0 rcollistvalues
    in
    let t = fun c ->
      shuffle grp (length cand_all0) cand_all0 dec_cand (fun d -> v d c) pi
        (rcolfunvalues c)
    in
    let w = fun c d -> t d c in
    let zkppermvw = fun c ->
      shuffle_zkp grp (length cand_all0) cand_all0 (fun d -> v d c) (fun d ->
        w d c) pi cpi s0 (rcolfunvalues c)
    in
    let b = fun c d -> decrypt_message grp privatekey (w c d) in
    let zkpdecw = fun c d ->
      construct_zero_knowledge_decryption_proof grp privatekey (w c d)
    in
    let s1 = matrix_ballot_valid_dec cand_all0 dec_cand b in
    if s1
    then let nm = fun c d -> homomorphic_addition grp (y c d) (m0 c d) in
         let x = Ecvalid (y, v, w, b, zkppermuv, zkppermvw, zkpdecw, cpi,
           zkpcpi, l, m0, nm, inbs, he)
         in
         ppartial_count_all_counted cand_all0 dec_cand grp bs l inbs nm x
    else let x = Ecinvalid (y, v, w, b, zkppermuv, zkppermvw, zkpdecw, cpi,
           zkpcpi, l, m0, inbs, he)
         in
         ppartial_count_all_counted cand_all0 dec_cand grp bs l (y :: inbs)
           m0 x

(** val pall_ballots_counted :
    'a1 list -> ('a1 -> 'a1 -> bool) -> group -> 'a1 eballot list -> ('a1
    eballot list, ('a1 -> 'a1 -> ciphertext, 'a1 eCount) sigT) sigT **)

let pall_ballots_counted cand_all0 dec_cand grp bs =
  let hs = ecount_all_ballot cand_all0 grp bs in
  let ExistT (encm, heg) = hs in
  ppartial_count_all_counted cand_all0 dec_cand grp bs bs [] encm heg

(** val decrypt_margin :
    'a1 list -> ('a1 -> 'a1 -> bool) -> group -> 'a1 eballot list -> ('a1 ->
    'a1 -> plaintext, 'a1 eCount) sigT **)

let decrypt_margin cand_all0 dec_cand grp bs =
  let hc = pall_ballots_counted cand_all0 dec_cand grp bs in
  let ExistT (i, s0) = hc in
  let ExistT (m0, hcount) = s0 in
  let decm = fun c d -> decrypt_message grp privatekey (m0 c d) in
  let zkpdecm = fun c d ->
    construct_zero_knowledge_decryption_proof grp privatekey (m0 c d)
  in
  ExistT (decm, (Ecdecrypt (i, m0, decm, zkpdecm, hcount)))

(** val pschulze_winners :
    'a1 list -> ('a1 -> 'a1 -> bool) -> group -> 'a1 eballot list -> ('a1 ->
    bool, 'a1 eCount) sigT **)

let pschulze_winners cand_all0 dec_cand grp bs =
  let s0 = decrypt_margin cand_all0 dec_cand grp bs in
  let ExistT (dm, hecount) = s0 in
  ExistT ((c_wins cand_all0 dec_cand dm), (Ecfin (dm,
  (c_wins cand_all0 dec_cand dm),
  (wins_loses_type_dec cand_all0 dec_cand dm), hecount)))

type cand =
| A
| B
| C

(** val cand_all : cand list **)

let cand_all =
  A :: (B :: (C :: []))

(** val cand_eq_dec : cand -> cand -> bool **)

let cand_eq_dec a b =
  match a with
  | A -> (match b with
          | A -> true
          | _ -> false)
  | B -> (match b with
          | B -> true
          | _ -> false)
  | C -> (match b with
          | C -> true
          | _ -> false)

(** val eschulze_winners_pf :
    group -> cand eballot list -> (cand -> bool, cand eCount) sigT **)

let eschulze_winners_pf =
  pschulze_winners cand_all cand_eq_dec

(* end of extracted code *)


(* print values *)

(*
let show_bool = function 
  | Lib.True -> "True"
  | Lib.False -> "False" *)

let rec nat_int = function
  | O -> 0
  | S n' -> 1 + nat_int n'
(*
let rec ocamllist = function
  | Nil -> []
  | Cons (h, t) -> h :: ocamllist t *)
                                  
let show_nat n = string_of_int (nat_int n)         

(*
let rec ocaml_pos = function
  | Lib.XH -> 1
  | p ->
     let rec ocaml_help t c =
       match t with
       | Lib.XH -> c
       | Lib.XO r -> ocaml_help r (2 * c)
       | Lib.XI r -> c + ocaml_help r (2 * c)
     in ocaml_help p 1

let ocaml_z = function
  | Lib.Z0 -> 0
  | Lib.Zpos p -> ocaml_pos p
  | Lib.Zneg p -> -1 * ocaml_pos p

let show_z p = string_of_int (ocaml_z p) *)
                             
let show_cand = function
  | A -> "A"
  | B -> "B"
  | C -> "C"
  (*| Lib.D -> "D"
  | Lib.E -> "E"
  | Lib.F -> "F"
  | Lib.G -> "G"
  | Lib.H -> "H"
  | Lib.I -> "I"
  | Lib.J -> "J"
  | Lib.K -> "K"
  | Lib.L -> "L"
  | Lib.N -> "N"
  | Lib.P -> "P"
  | Lib.Q -> "Q"
  | Lib.R -> "R"
  | Lib.T -> "T"
  | Lib.U -> "U"
  | Lib.V -> "V"
  | Lib.X -> "X"
  | Lib.Y -> "Y"
  | Lib.Z -> "Z"*)

(*
let compare x y =
  match Lib.cand_eq_dec x y with
  | Left -> true
  | _ -> false *)


let compare x y = cand_eq_dec x y

(*
let compare_pair x y =
  match x, y with
  | Lib.Pair (x1, y1), Lib.Pair (x2, y2) -> compare x1 x2 && compare y1 y2 *)
 
let cartesian l l' = 
          List.concat (List.map (fun e -> List.map (fun e' -> (e,e')) l') l)

let rec cross_prod_orig l = cartesian l l

                                                                  
let show_cand_pair (c1, c2) = "(" ^ show_cand c1 ^ "," ^ show_cand c2 ^ ")"

(*
let compare_truth x y =
  match x, y with
  | Lib.True, Lib.True | Lib.False, Lib.False -> true
  | _, _ -> false *)

let compare_truth x y = x = y
 
(* 
let show_coclosed f l =
  "[" ^ String.concat
          ","
          (List.map show_cand_pair  
          (List.filter (fun (x, y) -> compare_truth (f (Lib.Pair (x, y))) Lib.True)
                       (cross_prod_orig l))) ^ "]" *)

let show_coclosed f l =
  "[" ^ String.concat
          ","
          (List.map show_cand_pair
          (List.filter (fun (x, y) -> compare_truth (f (x, y)) true)
                       (cross_prod_orig l))) ^ "]"


let show_help f c d = show_cand c ^ show_cand d ^ Big.to_string (f c d)
  
let show_ballot f =
  String.concat " " (List.map (fun (c, d) -> show_help f c d) (cross_prod_orig cand_all))

let show_enc_pair (f, s) = 
        "(" ^ Big.to_string f ^ ", " ^ Big.to_string s ^ ")"

let show_enc_help f c d = show_cand c ^ show_cand d ^ show_enc_pair (f c d)

let show_enc_ballot f = 
    String.concat " " (List.map (fun (c, d) -> show_enc_help f c d) (cross_prod_orig cand_all))

let show_enc_marg m = show_enc_ballot m 

(*
let bool_b = function
  | Nil -> true
  | _ -> false *)

let bool_b = function
  | [] -> true
  | _ -> false

(*  
let show_list_inv_ballot = function
  | Nil ->"[]"
  | Cons (b, Nil) -> "[" ^ show_enc_ballot b ^ "]"
  | Cons (b, _) -> "[" ^ show_enc_ballot b ^ ",..]" *)

let show_list_inv_ballot = function
  | [] ->"[]"
  | [b] -> "[" ^ show_enc_ballot b ^ "]"
  | b :: _ -> "[" ^ show_enc_ballot b ^ ",..]"


let rec cross_prod = function
  | [] -> []
  | h :: t -> List.map (fun x -> (h, x)) t @ cross_prod t
                                                     
let show_pair c1 c2 n = show_cand c1 ^ show_cand c2 ^ ": " ^ Big.to_string n                                       

let show_marg m =
  "[" ^ String.concat
          " "
          (List.map (fun (x, y) -> show_pair x y (m x y)) (cross_prod_orig  cand_all))
  ^ "]"
      
let rec show_path = function
  | UnitT (x, y) -> show_cand x ^ " --> " ^ show_cand y
  | ConsT (x, _, _, p) -> show_cand x ^ " --> " ^ show_path p

(*
let rec show_winner g x xs =
  match xs with
  | [] -> ""
  | y :: ys -> if compare x y then show_winner g x ys
               else
                 match (g y) with
                 | ExistT (u, Pair (v, ExistT (f, _))) ->
                    "   for " ^ show_cand y ^ ": " ^ "path " ^
                      show_path v ^ " of strenght "  ^ show_z u ^  ", " ^
                        string_of_int (1 + ocaml_z u) ^ 
                          "-" ^ "coclosed set: " ^ show_coclosed f (ocamllist Lib.cand_all)
                       ^ (if ys = [] then " " else "\n")  ^ show_winner g x ys  *)

let rec show_winner g x xs =
  match xs with
  | [] -> ""
  | y :: ys -> if compare x y then show_winner g x ys
               else
                 match (g y) with
                 | ExistT (u, (v, ExistT (f, _))) ->
                    "   for " ^ show_cand y ^ ": " ^ "path " ^
                      show_path v ^ " of strenght "  ^ Big.to_string u ^  ", " ^
                        Big.to_string (Big.add_int 1 u) ^
                          "-" ^ "coclosed set: " ^ show_coclosed f cand_all
                       ^ (if ys = [] then " " else "\n")  ^ show_winner g x ys

(*                         
let show_loser g x =
  match g with
  | ExistT (u, ExistT (c, Pair (p, ExistT (f, _)))) ->
     "   exists " ^ show_cand c ^ ": " ^ "path " ^ show_path p ^ " of strength "
     ^ show_z u ^ ", " ^ show_z u ^ "-" ^ "coclosed set: " ^ show_coclosed f (ocamllist Lib.cand_all) *)


let show_loser g x =
  match g with
  | ExistT (u, ExistT (c, (p, ExistT (f, _)))) ->
     "   exists " ^ show_cand c ^ ": " ^ "path " ^ show_path p ^ " of strength "
     ^ Big.to_string u ^ ", " ^ Big.to_string u ^ "-" ^ "coclosed set: " ^ show_coclosed f cand_all
 
let show_cand f x =
  match f x with
  | Inl g -> "winning: " ^ show_cand x ^ "\n" ^ show_winner g x cand_all
  | Inr h -> "losing: " ^ show_cand x ^ "\n" ^ show_loser h x
                                                          
let rec add_string = function
  | 0 -> ""
  | n -> "-" ^ add_string (n - 1)
                            
let underline s = s ^ "\n" ^ add_string (String.length s) ^ "\n"



(*
let show_count l =
  let rec show_count_aux acc = function 
  | Ecax (us, encm, decm, zkpdec) -> (underline ("M: " ^ show_enc_marg m ^ ", Decrypted margin " ^ show_marg dm ^ ", Zero Knowledge Proof of Honest Decryption: " ^ Big.to_string v)) :: acc 
  | Ecvalid (u, v, w, b, zkppermuv, zkppermvw, zkpdecw, cpi, zkpcpi, us, m, nm, inbs, c) ->
     show_count_aux (underline (
       "V: [" ^ show_enc_ballot u ^ (if bool_b us then "]" else ",..]")  ^
         ", I:  " ^ show_list_inv_ballot inbs  ^ ", M: " ^ show_enc_marg m ^ ", Row Permuted Ballot: " ^ show_enc_ballot v ^
         ", Column Permuted Ballot: " ^ show_enc_ballot w ^
         ", Decryption of Permuted Ballot: " ^ show_ballot b ^ ", Zero Knowledge Proof of Row Permutation: " ^ Big.to_string zkppermuv ^ 
         ", Zero Knowledge Proof of Column Permutation: " ^ Big.to_string zkppermvw ^
         ", Zero Knowledge Proof of Decryption: " ^ Big.to_string zkpdecw) :: acc) c 
  | Ecinvalid (u, v, w, b, zkppermuv, zkppermvw, zkpdecw, cpi, zkpcpi, us, m, inbs, c)  ->
     show_count_aux (underline (
       "V: [" ^ show_enc_ballot u ^
         (if bool_b us then "]" else ",..]") ^ ", I: " ^ show_list_inv_ballot inbs ^ 
           ", M: " ^ show_enc_marg m ^ ", Row Permuted Ballot: " ^ show_enc_ballot v ^ 
           ", Column Permuted Ballot: " ^ show_enc_ballot w ^
           ", Decryption of Permuted Ballot: " ^ show_ballot b ^ ", Zero Knowledge Proof of Row Permutation: " ^ Big.to_string zkppermuv ^ 
           ", Zero Knowledge Proof of Column Permutation: " ^ Big.to_string zkppermvw ^
           ", Zero Knowledge Proof of Decryption: " ^ Big.to_string zkpdecw) :: acc) c
  | Ecdecrypt (inbs, encm, decm, zkpdecm, c) -> 
     show_count_aux (underline (
       "V: [], I: " ^ show_list_inv_ballot inbs ^ ", M: " ^ show_enc_marg m ^ ", DM: " ^ show_marg dm ^ 
       ", Zero Knowledge Proof of Decryption: " ^ Big.to_string zkpdecm) :: acc) c 
  | Ecfin (m, p, f, c) ->
     show_count_aux (underline (
       "DM: " ^ show_marg m ^
       String.concat "\n" (List.map (fun x -> show_cand f x) cand_all) ^ "\n") :: acc) c
in show_count_aux [] l  *)

let rec list_to_string = function []
 | [] -> ""
 | h :: t -> h ^ " " ^ list_to_string t

let show_row r = 
   let rw = List.map r cand_all in 
   let dec_value = List.map (fun x -> decrypt_message (Group (prime, generator, publickey)) privatekey x) rw in 
   list_to_string (List.map Big.to_string dec_value)  

let show_list u =
  let bl = List.map u cand_all in 
  String.concat "\n" (List.map show_row bl )
 
let rec show_count = function 
| Ecax (us, encm, decm, zkpdec) -> (underline ("M: " ^ show_enc_marg encm ^ ", Decrypted margin " ^ show_marg decm ))
| Ecvalid (u, v, w, b, zkppermuv, zkppermvw, zkpdecw, cpi, zkpcpi, us, m, nm, inbs, c) -> 
           (show_count c) ^ "\nShowing ballot u\n" ^ show_list u ^ "\nShowing row permuted v\n" ^ show_list v ^ "\nShowing column permuted w\n" ^ show_list w ^ "\nDecrypted ballot b\n" ^ show_ballot b  
| Ecinvalid (u, v, w, b, zkppermuv, zkppermvw, zkpdecw, cpi, zkpcpi, us, m, inbs, c) -> 
           show_count c ^ "\nShowing ballot u\n" ^ show_list u ^ "\nShowing row permuted v\n" ^ show_list v ^ "\nShowing column permuted w\n" ^ show_list w ^ "\nDecrypted ballot b\n" ^ show_ballot b
| Ecdecrypt (inbs, encm, decm, zkpdecm, c) -> show_count c 
| Ecfin (m, p, f, c) -> show_count c 












let cc c =
  match c with
  | 'A' -> A
  | 'B' -> B
  | 'C' -> C
  | _ -> failwith "more candidate"


(* use the same trick in coq for converting between list and function closure *)
let cand_eq x y = 
        match x, y with 
        | A, A -> true
        | B, B -> true
        | C, C -> true 
        | _, _ -> false

let rec bal_find c d = function
        | [] -> failwith "error "
        | (x, y, value) :: rest ->
                        if cand_eq c x && cand_eq d y then value
                        else bal_find c d rest

let balfun l = fun c d -> 
    bal_find c d l

let map f l =
  let rec map_aux acc = function
    | [] -> acc []
    | x :: xs -> map_aux (fun ys -> acc (f x :: ys)) xs
  in map_aux (fun ys -> ys) l 


let _ = 
  let e = Parser.prog Lexer.lexeme (Lexing.from_channel stdin) in
  let w = map (fun x -> map (fun (a, b, (c, d)) -> (cc a, cc b,  (Big.of_string c, Big.of_string d))) x) e in
  let v = map (fun x -> balfun x) w in
  match eschulze_winners_pf (Group (prime, generator, publickey)) v with
  | ExistT (f, y) ->  List.iter (fun x -> Format.printf "%s" x) [(show_count y)]

(* Format.printf "%s" (show_enc_marg f)  List.iter (fun x -> Format.printf "%s" x) (show_count y) *)







