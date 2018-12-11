let () = Java.init [| "-Djava.class.path=bin/ocaml-java.jar:/home/users/u5935541/Mukesh/Code/EncryptionSchulze/code/javacryptocode/jarfiles/unicrypt-2.3.jar:/home/users/u5935541/Mukesh/Code/EncryptionSchulze/code/javacryptocode/jarfiles/jnagmp-2.0.0.jar:/home/users/u5935541/Mukesh/Code/EncryptionSchulze/code/javacryptocode/jarfiles/jna-4.5.0.jar:/home/users/u5935541/Mukesh/Code/EncryptionSchulze/code/schulze.jar:." |]
let () = Printexc.record_backtrace true



class%java big_integer "java.math.BigInteger" =
object 
        initializer(create : string -> _)
        method multiply : big_integer -> big_integer = "multiply"
        method to_string : string = "toString"
end


class%java crypto_java "schulze.HelloWorld" = 
object
        method [@static] generate_privatekey : big_integer = "generateSK"
        method [@static] generate_publickey : big_integer -> big_integer = "generatePK"
        method [@static] enc_ballot_wrapper : big_integer array -> big_integer -> big_integer array = "encBallotWrapper"
end


let create_array_from_list lst =
    let len = List.length lst in
    let cls = Jclass.find_class "java/math/BigInteger" in
    let ballot = Jarray.create_object cls Java.null len in
    let rec loop i = function
        | b :: tl    ->
            Jarray.set_object ballot i b;
            loop (i + 1) tl
        | []        -> ()
    in
    loop 0 lst;
    ballot

(* We are assuming only 3 candidates for the moment *)    
let starting_margin = List.map string_of_int [0; 0; 0; 0; 0; 0; 0; 0; 0]
let plaintext = List.map (List.map string_of_int) [[0; 1; 1; 0; 0; 1; 0; 0; 0]; [0; 1; 1; 0; 0; 1; 0; 0; 0]; [0; 1; 1; 0; 0; 0; 0; 1; 0]; [0; 1; 1; 0; 0; 1; 0; 0; 0]; [0; 0; 0; 1; 0; 1; 1; 0; 0]; 
                 [0; 0; 0; 1; 0; 0; 1; 1; 0]; [0; 1; 0; 0; 0; 0; 1; 1; 0]; [0; 1; 1; 0; 0; 0; 0; 1; 0]; [0; 0; 1; 1; 0; 1; 0; 0; 0]; [0; 1; 1; 0; 0; 1; 0; 0; 0]]


let encrypt_margin pkey bal = Crypto_java.enc_ballot_wrapper bal pkey
(*    
let () = 
   let strl = ["1"; "1"; "1"; "1"; "1"; "1"; "1"; "1"] in  
   let big_num = List.map Big_integer.create strl in
   let ballot = create_array_from_list big_num in
   let len = List.length strl in 
   let f = List.nth big_num 0 in 
   let s = List.nth big_num 1 in 
   print_endline(Big_integer.to_string t);
   for i = 0 to (len - 1) do
        print_endline (Big_integer.to_string (Jarray.get_object ballot i))
   done *)

(* Three candidates, A B C 
   (A, A, (0, 0)); (A, B, (1, 0)); (A, C, (1, 0)); (B, A, (0, 0)); (B, B, (0, 0)); (B, C, (0, 0)); (C, A, (0, 0)); (C, B, (1, 0)); (C, C, (0, 0)) *)

(* Don't expose any internal class so try to operate in BigInteger world because it will make the code and life easier *)


let () = 
 let prikey = Crypto_java.generate_privatekey () in
 let pubkey = Crypto_java.generate_publickey prikey in 
 let zero_marg = encrypt_margin pubkey (create_array_from_list (List.map Big_integer.create starting_margin)) in 
 let len = 18 in
 print_endline (Big_integer.to_string prikey);
 print_endline (Big_integer.to_string pubkey);
 for i = 0 to (len - 1) do
        print_endline (Big_integer.to_string (Jarray.get_object zero_marg i))
 done




