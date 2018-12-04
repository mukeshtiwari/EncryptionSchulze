let () = Java.init [| "-Djava.class.path=ocaml-java/bin/ocaml-java.jar:javacryptocode/jarfiles/unicrypt-2.3.jar:javacryptocode/jarfiles/jnagmp-2.0.0.jar:javacryptocode/jarfiles/jna-4.5.0.jar:." |]

(* Java Big integer binding *)
class%java big_integer "java.math.BigInteger" =
object 
        initializer(create : string -> _)
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
end



class%java gstar_mod "ch.bfh.unicrypt.math.algebra.multiplicative.classes.GStarMod" = 
object 
        method to_string : string = "toString"
end


class%java gstar_mod_prime "ch.bfh.unicrypt.math.algebra.multiplicative.classes.GStarModPrime" = 
object
        inherit gstar_mod
        method to_string : string = "toString"
end



class%java gstar_mod_safe_prime "ch.bfh.unicrypt.math.algebra.multiplicative.classes.GStarModSafePrime" =
object
        inherit gstar_mod_prime
        method [@static] get_instance : safe_prime -> gstar_mod_safe_prime = "getInstance"
        method to_string : string = "toString"
end


class%java gstar_mod_element "ch.bfh.unicrypt.math.algebra.multiplicative.classes.GStarModElement" =
object
        initializer(get_element : gstar_mod -> big_integer -> _) 
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

(* Construct generator data structure *)
let generator_from_group grp gen = 
    Gstar_mod_element.get_element grp gen 

let () = 
   let safep = safe_prime (big_int_from_string  "170141183460469231731687303715884114527") in
   let gp = group_from_safe_prime safep in
   let gen = generator_from_group gp (big_int_from_string "4") in  
   print_endline (Prime.to_string safep);
   print_endline (Gstar_mod_safe_prime.to_string gp);
   print_endline (Gstar_mod_element.to_string gen)




(*

class%java element "ch.bfh.unicrypt.math.algebra.general.interfaces.Element" = object end


class%java zmod_prime "ch.bfh.unicrypt.math.algebra.dualistic.classes.ZModPrime" = 
object
        method to_string : string = "toString"
end



class%java zmod_element "ch.bfh.unicrypt.math.algebra.dualistic.classes.ZModElement" = 
object 
        
       initializer(get_element : zmod_prime -> big_integer -> _)
       method to_string : string = "toString"
end

 
(* In this class, 
 * gstar_mod_safe_prime extends gstar_mod_prime extends gstar_mod *)
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


class%java gstar_mod_element "ch.bfh.unicrypt.math.algebra.multiplicative.classes.GStarModElement" =
object 
       inherit element
       initializer(get_element : gstar_mod -> big_integer -> _)    
       method to_string : string = "toString"
end 


class%java elgamal_encryption_scheme "ch.bfh.unicrypt.crypto.schemes.encryption.classes.ElGamalEncryptionScheme" = 
object
        inherit element
        method [@static] get_scheme : element -> elgamal_encryption_scheme = "getInstance"
        method to_string : string = "toString"
end 


(*
let prime  = "170141183460469231731687303715884114527"
let gen = "4"
let privatekey = "60245260967214266009141128892124363925"
let publickey = "49228593607874990954666071614777776087"
*)


let prime : 'a = Safe_prime.get_instance (Big_integer.create "170141183460469231731687303715884114527")
let group : 'a = Gstar_mod_safe_prime.get_instance prime
let generator : 'a = Gstar_mod_element.get_element group (Big_integer.create "4")
let elgamalscheme : 'a = Elgamal_encryption_scheme.get_scheme generator
let publickey = Gstar_mod_element.get_element group (Big_integer.create "49228593607874990954666071614777776087")



let () = 
   let p = Prime.get_random_instance 10 in 
   print_endline (Prime.to_string p)
(* 
let () = 
   let prime = Safe_prime.get_smallest_instance 128 in
   let group = Gstar_mod_safe_prime.get_instance prime in
   let generator = Gstar_mod_element.get_element group (Big_integer.create "4") in 
   let elscheme = Elgamal_encryption_scheme.get_scheme generator in
   let publickey = Gstar_mod_element.get_element group (Big_integer.create "49228593607874990954666071614777776087") in
   let zmodel = Gstar_mod_prime.get_zmod_order group in
   print_endline (Safe_prime.to_string prime);
   print_endline (Gstar_mod_safe_prime.to_string group);
   print_endline (Gstar_mod_element.to_string generator);
   print_endline (Elgamal_encryption_scheme.to_string elscheme);
   print_endline (Gstar_mod_element.to_string publickey);
   print_endline (Zmod_prime.to_string zmodel) *)



*)
