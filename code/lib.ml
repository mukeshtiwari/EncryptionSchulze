
open Big
open Lexer
open Parser

let () = Java.init [| "-Djava.class.path=../ocaml-java/bin/ocaml-java.jar:javacryptocode/jarfiles/unicrypt-2.3.jar:javacryptocode/jarfiles/jnagmp-2.0.0.jar:javacryptocode/jarfiles/jna-4.5.0.jar:schulze.jar:." |]
let () = Printexc.record_backtrace true


class%java big_integer "java.math.BigInteger" =
object 
        initializer(create : string -> _)
        method multiply : big_integer -> big_integer = "multiply"
        method to_string : string = "toString"
end



class%java crypto_java "schulze.CryptoWrapper" = 
object
        (* Prime, generator, Publickey, message, returns ciphertext *)
        method [@static] encrypt_message_ocaml : string -> string -> string -> string -> string = "encryptMessage"
        (* Prime, generator, privatekey, pubkey, ciphertext, and returns zero knowledge proof string *)
        method [@static] generate_decryption_zero_knowledge_ocaml : string -> string -> string -> string -> string -> string = "constructDecryptionZeroKnowledgeProof"
end




type ('a, 'p) sigT =
| ExistT of 'a * 'p

type plaintext = Big.big_int

type ciphertext = Big.big_int * Big.big_int

type 'cand eballot = 'cand -> 'cand -> ciphertext

type prime = string (* AXIOM TO BE REALIZED *)

type generator = string (* AXIOM TO BE REALIZED *)

type pubkey = string (* AXIOM TO BE REALIZED *)

type prikey = string (* AXIOM TO BE REALIZED *)

(** val prime0 : prime **)

let prime0 =
  "170141183460469231731687303715884114527"

(** val gen : generator **)

let gen =
  "4"

(** val privatekey : prikey **)

let privatekey =
  "60245260967214266009141128892124363925"

(** val publickey : pubkey **)

let publickey =
  "49228593607874990954666071614777776087"

type group =
| Group of prime * generator * pubkey


(* converts string to char list *)
let explode s =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) []

(** val encrypt_message : group -> plaintext -> ciphertext **)

let encrypt_message (Group (prime, gen, pubkey)) mess = 
  let ciphertext = Crypto_java.encrypt_message_ocaml prime gen pubkey (Big.to_string mess) in 
  match Str.split (Str.regexp ",") ciphertext with
  | fs :: ss :: _ -> (Big.of_string fs, Big.of_string ss)
  | _ -> failwith "the value return has no comma" 


(** val construct_zero_knowledge_decryption_proof :
    group -> prikey -> ciphertext -> char list **)

let construct_zero_knowledge_decryption_proof (Group (prime, gen, pubkey)) prikey (c1, c2) = 
  let ciphertext = (Big.to_string c1) ^ "," ^ (Big.to_string c2) in 
  let zkp = Crypto_java. generate_decryption_zero_knowledge_ocaml prime gen prikey pubkey ciphertext in 
  explode zkp

type 'cand eCount =
| Ecax of 'cand eballot list * ('cand -> 'cand -> ciphertext)
   * ('cand -> 'cand -> plaintext) * ('cand -> 'cand -> char list)

(** val ecount_all_ballot :
    group -> 'a1 eballot list -> ('a1 -> 'a1 -> ciphertext, 'a1 eCount) sigT **)

let ecount_all_ballot grp bs =
  ExistT ((fun _ _ -> encrypt_message grp Big.zero), (Ecax (bs, (fun _ _ ->
    encrypt_message grp Big.zero), (fun _ _ -> Big.zero), (fun _ _ ->
    construct_zero_knowledge_decryption_proof grp privatekey
      (encrypt_message grp Big.zero)))))

type cand =
| A
| B
| C

(** val unicrypt_encryption_library_call :
    cand eballot list -> (cand -> cand -> ciphertext, cand eCount) sigT **)

let unicrypt_encryption_library_call =
  ecount_all_ballot (Group (prime0, gen, publickey))

(* Printing function *)
let cand_all = A :: (B :: (C :: []))



let show_cand = function
  | A -> "A"
  | B -> "B"
  | C -> "C"

let cartesian l l' = 
  List.concat (List.map (fun e -> List.map (fun e' -> (e,e')) l') l)


let rec cross_prod_orig l = cartesian l l

                                                                  
let show_cand_pair (c1, c2) = "(" ^ show_cand c1 ^ "," ^ show_cand c2 ^ ")"

let compare_truth x y = x = y

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

let bool_b = function
  | [] -> true
  | _ -> false

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


let rec add_string = function
  | 0 -> ""
  | n -> "-" ^ add_string (n - 1)
                            
let underline s = s ^ "\n" ^ add_string (String.length s) ^ "\n"

let cl2s cl = String.concat "" (List.map (String.make 1) cl)

let show_zkp v =
    "[" ^ String.concat
          " "
          (List.map (fun (x, y) -> "(" ^ (cl2s (v x y)) ^")") (cross_prod_orig  cand_all))
      ^ "]"
 

let show_count l =
  let rec show_count_aux acc = function 
  | Ecax (_, m, dm, v) -> (underline ("M: " ^ show_enc_marg m ^ ", Decrypted margin " ^ show_marg dm ^ ", Zero Knowledge Proof of Honest Decryption: " ^ show_zkp v)) :: acc 
  in show_count_aux [] l   

(* Main function *)
let cc c =
  match c with
  | 'A' -> A
  | 'B' -> B
  | 'C' -> C
  | _ -> failwith "more candidate"


let balfun l = 
   match l with
   | [(A, A, b1); (A, B, b2); (A, C, b3); (B, A, b4); (B, B, b5); (B, C, b6); (C, A, b7); (C, B, b8); (C, C, b9)] -> 
      let
        f c d = match c, d with
        | A, A -> b1
        | A, B -> b2
        | A, C -> b3
        | B, A -> b4
        | B, B -> b5
        | B, C -> b6
        | C, A -> b7
        | C, B -> b8
        | C, C -> b9
      in  f
   | _ -> failwith "failed to match pattern" 


let map f l =
  let rec map_aux acc = function
    | [] -> acc []
    | x :: xs -> map_aux (fun ys -> acc (f x :: ys)) xs
  in map_aux (fun ys -> ys) l 


let _ = 
  let e = Parser.prog Lexer.lexeme (Lexing.from_channel stdin) in
  let w = map (fun x -> map (fun (a, b, (c, d)) -> (cc a, cc b,  (Big.of_string c, Big.of_string d))) x) e in
  let v = map (fun x -> balfun x) w in
  match unicrypt_encryption_library_call v with
  | ExistT (f, y) -> (* Format.printf "%s" (show_enc_marg f) *) List.iter (fun x -> Format.printf "%s" x) (show_count y)
