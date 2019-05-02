open Lexer
open Parser
open Big
open Cryptobinding
open Lib
open Derivation

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
  match eschulze_winners_pf prime generator privatekey publickey encrypt_message decrypt_message construct_zero_knowledge_decryption_proof generatePermutation generateS 
                            generatePermutationCommitment zkpPermutationCommitment homomorphic_addition generateR shuffle shuffle_zkp v with
  | ExistT (f, y) ->  (* List.iter (fun x -> print_endline (string_of_bool (f x))) [A; B; C] *) List.iter (fun x -> Format.printf "%s" x) (show_count y)
  
(* Format.printf "%s" (show_enc_marg f)  List.iter (fun x -> Format.printf "%s" x) (show_count y) *)

