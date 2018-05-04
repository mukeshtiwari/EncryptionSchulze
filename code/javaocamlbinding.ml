let () = Java.init [| "-Djava.class.path=ocaml-java/bin/ocaml-java.jar:javacryptocode/jarfiles/unicrypt-2.3.jar:javacryptocode/jarfiles/jnagmp-2.0.0.jar:javacryptocode/jarfiles/jna-4.5.0.jar:schulze.jar:." |]
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
        method [@static] enc_ballot_mult_wrapper : big_integer array -> big_integer array -> big_integer array = "encBallotMultWrapper"
        method [@static] dec_ballot_wrapper : big_integer array -> big_integer -> big_integer array = "decBallot"
        method [@static] dec_ballot_zkp_wrapper : big_integer array -> big_integer -> string = "decBallotZeroknowledge"
        method [@static] row_permutation_wrapper : big_integer array -> big_integer -> big_integer array = "rowShuffle"
        method [@static] row_permutation_zkp_wrapper : big_integer array -> big_integer -> string = "rowShuffleZKP"
        method [@static] column_permutation_wrapper : big_integer array -> big_integer -> big_integer array = "columnShuffle"
        method [@static] column_permutation_zkp_wrapper : big_integer array -> big_integer -> string = "columnShuffleZKP"
end


(* this function creates java array from list of strings*)
let create_array_from_list lst =
    let len = List.length lst in
    let nlst = List.map Big_integer.create lst in
    let cls = Jclass.find_class "java/math/BigInteger" in
    let ballot = Jarray.create_object cls Java.null len in
    let rec loop i = function
        | b :: tl    ->
            Jarray.set_object ballot i b;
            loop (i + 1) tl
        | []        -> ()
    in
    loop 0 nlst;
    ballot

(* this function creates ocaml list of strings from java array *)
let create_list_from_array arr = 
    let len = Jarray.length arr in 
    let rec loop i acc = 
     if i >= len then (List.rev acc)
     else let v = Big_integer.to_string (Jarray.get_object arr i) in
           loop (i + 1) (v :: acc) in
    loop 0 []


(* This function takes list of string from lib.ml code and it is basically a plaintext ballot which is encrypte here and returned as list of string *)
let enc_ballot lst publickey = 
  let arr = create_array_from_list lst in
  let encarry = Crypto_java.enc_ballot_wrapper arr publickey in 
  create_list_from_array encarry

(* this function takes two list of strings (which are basically big integers in string) and returns the sum *)
let homomorphic_addition lst1 lst2 = 
  let arr1 = create_array_from_list lst1 in
  let arr2 = create_array_from_list lst2 in
  let arr3 = Crypto_java.enc_ballot_mult_wrapper arr1 arr2 in
  create_list_from_array arr3

(* This function decrypts encrypted ballot *)
let dec_ballot lst privatekey = 
  let arr = create_array_from_list lst in 
  let decarr = Crypto_java.dec_ballot_wrapper arr privatekey in
  create_list_from_array decarr

(* this function is zero knowledge proof of decryption *)
let dec_ballot_zkp lst privatekey = 
  let arr = create_array_from_list lst in
  Crypto_java.dec_ballot_zkp_wrapper arr privatekey 

(* This function calculates row permuted array *)  
let row_perm lst publickey = 
  let arr = create_array_from_list lst in
  let rowpermarray = Crypto_java.row_permutation_wrapper arr publickey in 
  create_list_from_array rowpermarray

(* return the zkp of row permuted array *)
let row_perm_zkp lst publickey = 
  let arr = create_array_from_list lst in
  Crypto_java.row_permutation_zkp_wrapper arr publickey 

(* this function calculates column permuted array *)
let column_perm lst publickey = 
  let arr = create_array_from_list lst in 
  let colpermarray = Crypto_java.column_permutation_wrapper arr publickey in 
  create_list_from_array colpermarray

let column_perm_zkp lst publickey = 
  let arr = create_array_from_list lst in 
  Crypto_java.column_permutation_zkp_wrapper arr publickey
  
(*                 
let _ = 
   let lst = List.map string_of_int [0; 0; 0; 0; 0; 0; 0; 0; 0] in 
   let b = create_list_from_array (create_array_from_list lst) in 
   List.iter (fun x -> print_endline x) b *)

(* We are assuming only 3 candidates for the moment *)    
(*
let starting_margin = List.map string_of_int [0; 0; 0; 0; 0; 0; 0; 0; 0]
let plaintext = List.map (List.map string_of_int) [[0; 1; 1; 0; 0; 1; 0; 0; 0]; [0; 1; 1; 0; 0; 1; 0; 0; 0]; [0; 1; 1; 0; 0; 0; 0; 1; 0]; [0; 1; 1; 0; 0; 1; 0; 0; 0]; [0; 0; 0; 1; 0; 1; 1; 0; 0]; 
                 [0; 0; 0; 1; 0; 0; 1; 1; 0]; [0; 1; 0; 0; 0; 0; 1; 1; 0]; [0; 1; 1; 0; 0; 0; 0; 1; 0]; [0; 0; 1; 1; 0; 1; 0; 0; 0]; [0; 1; 1; 0; 0; 1; 0; 0; 0]]
*)
let invalid_ballot = (List.map string_of_int [1;1;1;1;1;1;1;1;1])






let _ = 
 let pkey = Big_integer.create "49228593607874990954666071614777776087" in 
 let skey = Big_integer.create "60245260967214266009141128892124363925" in
 let encinvbal = enc_ballot invalid_ballot pkey in
 let rperm = row_perm encinvbal pkey in 
 let cperm = column_perm rperm pkey in 
 let decinvbal = dec_ballot cperm skey in
 List.iter (fun x -> print_endline x) encinvbal;
 List.iter (fun x -> print_endline x) rperm;
 List.iter (fun x -> print_endline x) cperm;
 List.iter (fun x -> print_endline x) decinvbal




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

(*
let _ =  
   let prikey = Crypto_java.generate_privatekey () in
   let pubkey = Crypto_java.generate_publickey prikey in 
   let zero_marg = encrypt_margin pubkey (create_array_from_list (List.map Big_integer.create starting_margin)) in
   let data_ballot = List.map (fun x -> create_array_from_list (List.map Big_integer.create x)) plaintext in
   let enc_ballot = List.map (fun x -> encrypt_margin pubkey x) data_ballot in 
   print_endline ("private key = " ^ (Big_integer.to_string prikey));
   print_endline ("public key = " ^ (Big_integer.to_string pubkey));
   for i = 0 to 17 do
        print_endline (Big_integer.to_string (Jarray.get_object zero_marg i))
   done;
   print_endline ("finished zero margin encryption");
   for i = 0 to 9 do
        print_endline "starting to encrypt ballot";
        for j = 0 to 17 do
                 print_endline (Big_integer.to_string (Jarray.get_object (List.nth enc_ballot i) j))
        done;
        print_endline "finished encryption";
   done;
*)



