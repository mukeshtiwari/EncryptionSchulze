open Lib
open Parser
open Lexer
open Derivation
(*       
let ocamlcoq l =
  let rec map_aux acc = function
    | [] -> acc Nil
    | x :: xs -> map_aux (fun ys -> acc (Cons (x, ys))) xs
  in
  map_aux (fun ys -> ys) l
        
     
let rec ocamlnat n =
  match n with
  | 0 -> Z0
  | 1 -> Zpos XH
  | _ -> failwith "something else"
*)
           
let cc c =
  match c with
  | 'A' -> A
  | 'B' -> B
  | 'C' -> C
  (*| 'D' -> D
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
  | 'Y' -> Y
  | 'Z' -> Z *)
  | _ -> failwith "failed"
            
let balfun l = 
   match l with
   | [(A, A, b1); (A, B, b2); (A, C, b3); (B, A, b4); (B, B, b5); (B, C, b6); (C, A, b7); (C, B, b8); (C, C, b9) 
   (* (D, b4); (E, b5); (F, b6); (G, b7); (H, b8); (I, b9); (J, b10); (K, b11); (L, b12); (N, b13); (P, b14); (Q, b15); (R, b16); (T, b17); (U, b18); (V, b19); 
      (X, b20); (Y, b21); (Z, b22)*)] -> 
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
 
 
 (*       | D -> b4
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
        | Y -> b21
        | Z -> b22*)
        | _, _ -> failwith "failed to match"
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
  let w = map (fun x -> map (fun (a, b, (c, d)) -> (cc a, cc b,  (Big.of_int c, Big.of_int d))) x) e in
  let v = map (fun x -> balfun x) w in
  match schulze_winners_pf v with
  | ExistT (f, y) ->
     List.iter (fun x -> Format.printf "%s" x) (show_count y)
                    (*                
     List.iter (fun x -> Format.printf "%s\n"  (string_of_bool (f x))) [A; B; C]
          *)                                        
               
   

     
