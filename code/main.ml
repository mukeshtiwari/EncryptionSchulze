open Lib
open Parser
open Lexer
open Derivation

       
let ocamlcoq l =
  let rec map_aux acc = function
    | [] -> acc Nil
    | x :: xs -> map_aux (fun ys -> acc (Cons (x, ys))) xs
  in
  map_aux (fun ys -> ys) l
        
     
let rec ocamlnat n =
  match n with
  | 0 -> O
  | _ -> S (ocamlnat (n -1))

           
let cc c =
  match c with
  | 'A' -> A
  | 'B' -> B
  | 'C' -> C
  | 'D' -> D
  | 'E' -> E
  | 'F' -> F
  | 'G' -> G
  | 'H' -> H
  | 'I' -> I
  | 'J' -> J
  | 'K' -> K
  | 'L' -> L
  | 'N' -> N
  | 'P' -> P
  | 'Q' -> Q
  | 'R' -> R
  | 'T' -> T
  | 'U' -> U
  | 'V' -> V
  | 'X' -> X
  (*| 'Y' -> Y
  | 'Z' -> Z *)
  | _ -> failwith "failed"
            
let balfun l = 
   match l with
   | [(A, b1); (B, b2); (C, b3); (D, b4); (E, b5); (F, b6); (G, b7); (H, b8); (I, b9); (J, b10); (K, b11); (L, b12); (N, b13); (P, b14); (Q, b15); (R, b16); (T, b17); (U, b18); (V, b19); 
      (X, b20)(*; (Y, b21); (Z, b22)*)] -> 
      let
        f c = match c with
        | A -> b1
        | B -> b2
        | C -> b3
        | D -> b4
        | E -> b5
        | F -> b6
        | G -> b7
        | H -> b8
        | I -> b9
        | J -> b10
        | K -> b11
        | L -> b12
        | N -> b13
        | P -> b14
        | Q -> b15
        | R -> b16
        | T -> b17
        | U -> b18
        | V -> b19
        | X -> b20
        (*| Y -> b21
        | Z -> b22*)
        | _ -> failwith "failed to match"
      in  f
   | _ -> failwith "failed to match pattern" 

                   
let map f l =
  let rec map_aux acc = function
    | [] -> acc []
    | x :: xs -> map_aux (fun ys -> acc (f x :: ys)) xs
  in
  map_aux (fun ys -> ys) l
                            

let _ = 
  let e = Parser.prog Lexer.lexeme (Lexing.from_channel stdin) in
  let w = map (fun x -> map (fun (a, b) -> (cc a, ocamlnat b)) x) e in
  let v = map (fun x -> balfun x) w in
  match schulze_winners_pf (ocamlcoq v) with
  | ExistT (f, (ExistT (y, __))) ->
     List.iter (fun x -> Format.printf "%s" x ) (show_count y)
                                                 (*
     List.iter (fun x -> Format.printf "%s\n"  (show_bool (f x))) [A; B; C; D]
                                                  *)
               
   

     
