open Lib
open Printf
open Big
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
  | Lib.A -> "A"
  | Lib.B -> "B"
  | Lib.C -> "C"
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


let compare x y = Lib.cand_eq_dec x y

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
  String.concat " " (List.map (fun (c, d) -> show_help f c d) (cross_prod_orig Lib.cand_all))

let show_enc_pair (f, s) = 
        "(" ^ Big.to_string f ^ ", " ^ Big.to_string s ^ ")"

let show_enc_help f c d = show_cand c ^ show_cand d ^ show_enc_pair (f c d)

let show_enc_ballot f = 
    String.concat " " (List.map (fun (c, d) -> show_enc_help f c d) (cross_prod_orig Lib.cand_all))

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
          (List.map (fun (x, y) -> show_pair x y (m x y)) (cross_prod_orig  Lib.cand_all))
  ^ "]"
      
let rec show_path = function
  | Lib.UnitT (x, y) -> show_cand x ^ " --> " ^ show_cand y
  | Lib.ConsT (x, _, _, p) -> show_cand x ^ " --> " ^ show_path p

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
                          "-" ^ "coclosed set: " ^ show_coclosed f Lib.cand_all
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
     ^ Big.to_string u ^ ", " ^ Big.to_string u ^ "-" ^ "coclosed set: " ^ show_coclosed f Lib.cand_all
 
let show_cand f x =
  match f x with
  | Inl g -> "winning: " ^ show_cand x ^ "\n" ^ show_winner g x Lib.cand_all
  | Inr h -> "losing: " ^ show_cand x ^ "\n" ^ show_loser h x
                                                          
let rec add_string = function
  | 0 -> ""
  | n -> "-" ^ add_string (n - 1)
                            
let underline s = s ^ "\n" ^ add_string (String.length s) ^ "\n"

(*
let rec show_count = function
  | Lib.Ax (_, _, v) -> "Zero knowledge proof of m being zero encrypted matrix " ^ show_z v
  | Lib.Cvalid (u, v, b, zkppermuv, zkpdecv, us, m, nm, inbs, c) ->
     show_count c ^ underline (
       "V: [" ^ show_enc_ballot u ^ (if bool_b us then "]" else ",..]")  ^
         ", I:  " ^ show_list_inv_ballot inbs  ^ ", M: " ^ show_enc_marg m ^ "Permuted ballot: " ^ show_enc_ballot v ^
       " Decryption of permuted ballot " ^ show_ballot b ^ " zero knowledge proof of permutations " ^ show_z zkppermuv ^ 
       " zero knowledge proof of decryption " ^ show_z zkpdecv) 
  | Lib.Cinvalid (u, v, b, zkppermuv, zkpdecv, us, m, inbs, c)  ->
     show_count c ^ underline (
       "V: [" ^ show_enc_ballot u ^
         (if bool_b us then "]" else ",..]") ^ ", I: " ^ show_list_inv_ballot inbs ^ 
           ", M: " ^ show_enc_marg m ^ " Permuted ballot: " ^ show_enc_ballot v ^ 
         " Decryption of permuted ballot " ^ show_ballot b ^ "zero knowledge proof of permutation " ^ show_z zkppermuv ^
         " zero knowledge proof of decryption " ^ show_z zkpdecv)
  | Lib.Cdecrypt (inbs, m, dm, zkpdecm, c) -> 
     show_count c ^ underline (
             "Encrypted margin " ^ show_enc_marg m ^ " Decrypted margin " ^ show_marg dm ^ " zero knowledge proof of decryption " ^ 
             show_z zkpdecm)
  | Lib.Fin (m, p, f, c) ->
     show_count c ^ underline (
       "M: " ^ show_marg m )
     ^ String.concat "\n" (List.map (fun x -> show_cand f x) (ocamllist Lib.cand_all))
     ^ "\n" *)
(*
let rec show_count = function
  | Lib.Ax (_, _, v) -> "Zero knowledge proof of m being zero encrypted matrix " ^ Big.to_string v
  | Lib.Cvalid (u, v, b, zkppermuv, zkpdecv, us, m, nm, inbs, c) ->
     show_count c ^ underline (
       "V: [" ^ show_enc_ballot u ^ (if bool_b us then "]" else ",..]")  ^
         ", I:  " ^ show_list_inv_ballot inbs  ^ ", M: " ^ show_enc_marg m ^ "Permuted ballot: " ^ show_enc_ballot v ^
       " Decryption of permuted ballot " ^ show_ballot b ^ " zero knowledge proof of permutations " ^ Big.to_string zkppermuv ^
       " zero knowledge proof of decryption " ^ Big.to_string zkpdecv)
  | Lib.Cinvalid (u, v, b, zkppermuv, zkpdecv, us, m, inbs, c)  ->
     show_count c ^ underline (
       "V: [" ^ show_enc_ballot u ^
         (if bool_b us then "]" else ",..]") ^ ", I: " ^ show_list_inv_ballot inbs ^
           ", M: " ^ show_enc_marg m ^ " Permuted ballot: " ^ show_enc_ballot v ^
         " Decryption of permuted ballot " ^ show_ballot b ^ "zero knowledge proof of permutation " ^ Big.to_string zkppermuv ^
         " zero knowledge proof of decryption " ^ Big.to_string zkpdecv)
  | Lib.Cdecrypt (inbs, m, dm, zkpdecm, c) ->
     show_count c ^ underline (
             "Encrypted margin " ^ show_enc_marg m ^ " Decrypted margin " ^ show_marg dm ^ " zero knowledge proof of decryption " ^
             Big.to_string zkpdecm)
  | Lib.Fin (m, p, f, c) ->
     show_count c ^ underline (
       "M: " ^ show_marg m )
     ^ String.concat "\n" (List.map (fun x -> show_cand f x) Lib.cand_all)
     ^ "\n"
*)

(*
let show_count l =
  let rec show_count_aux acc = function 
  | Lib.Ax (_, _) -> acc 
  | Lib.Cvalid (u, us, m, nm, inbs, c) ->
     show_count_aux (underline (
       "V: [" ^ show_ballot u ^ (if bool_b us then "]" else ",..]")  ^
         ", I:  " ^ show_list_inv_ballot inbs  ^ ", M: " ^ show_marg m ) :: acc) c 
  | Lib.Cinvalid (u, us, m, inbs, c)  ->
     show_count_aux (underline (
       "V: [" ^ show_ballot u ^
         (if bool_b us then "]" else ",..]") ^ ", I: " ^ show_list_inv_ballot inbs ^ 
           ", M: " ^ show_marg m ) :: acc) c
  | Lib.Fin (m, ls, p, f, c) ->
     show_count_aux ((underline (
       "V: [], I: " ^ show_list_inv_ballot ls ^ ", M: " ^ show_marg m )
     ^ String.concat "\n" (List.map (fun x -> show_cand f x) (ocamllist Lib.cand_all))
     ^ "\n") :: acc) c
  in show_count_aux [] l *)


let show_count l =
  let rec show_count_aux acc = function 
  | Lib.Ax (_, m, dm, v) -> (underline ("M: " ^ show_enc_marg m ^ ", Decrypted margin " ^ show_marg dm ^ ", Zero Knowledge Proof of Honest Decryption: " ^ Big.to_string v)) :: acc 
  | Lib.Cvalid (u, v, w, b, zkppermuv, zkppermvw, zkpdecw, us, m, nm, inbs, c) ->
     show_count_aux (underline (
       "V: [" ^ show_enc_ballot u ^ (if bool_b us then "]" else ",..]")  ^
         ", I:  " ^ show_list_inv_ballot inbs  ^ ", M: " ^ show_enc_marg m ^ ", Row Permuted Ballot: " ^ show_enc_ballot v ^
         ", Column Permuted Ballot: " ^ show_enc_ballot w ^
         ", Decryption of Permuted Ballot: " ^ show_ballot b ^ ", Zero Knowledge Proof of Row Permutation: " ^ Big.to_string zkppermuv ^ 
         ", Zero Knowledge Proof of Column Permutation: " ^ Big.to_string zkppermvw ^
         ", Zero Knowledge Proof of Decryption: " ^ Big.to_string zkpdecw) :: acc) c 
  | Lib.Cinvalid (u, v, w, b, zkppermuv, zkppermvw, zkpdecw, us, m, inbs, c)  ->
     show_count_aux (underline (
       "V: [" ^ show_enc_ballot u ^
         (if bool_b us then "]" else ",..]") ^ ", I: " ^ show_list_inv_ballot inbs ^ 
           ", M: " ^ show_enc_marg m ^ ", Row Permuted Ballot: " ^ show_enc_ballot v ^ 
           ", Column Permuted Ballot: " ^ show_enc_ballot w ^
           ", Decryption of Permuted Ballot: " ^ show_ballot b ^ ", Zero Knowledge Proof of Row Permutation: " ^ Big.to_string zkppermuv ^ 
           ", Zero Knowledge Proof of Column Permutation: " ^ Big.to_string zkppermvw ^
           ", Zero Knowledge Proof of Decryption: " ^ Big.to_string zkpdecw) :: acc) c
  | Lib.Cdecrypt (inbs, m, dm, zkpdecm, c) -> 
     show_count_aux (underline (
       "V: [], I: " ^ show_list_inv_ballot inbs ^ ", M: " ^ show_enc_marg m ^ ", DM: " ^ show_marg dm ^ 
       ", Zero Knowledge Proof of Decryption: " ^ Big.to_string zkpdecm) :: acc) c 
  | Lib.Fin (m, p, f, c) ->
     show_count_aux (underline (
       "DM: " ^ show_marg m ^
       String.concat "\n" (List.map (fun x -> show_cand f x) Lib.cand_all) ^ "\n") :: acc) c
  in show_count_aux [] l 
