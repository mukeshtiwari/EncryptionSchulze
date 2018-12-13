open Big
open Cryptobinding
open Derivation


(* Infrastructure *)
let prime = big_int_from_string  "170141183460469231731687303715884114527"
let generator = big_int_from_string "4"
let publickey = big_int_from_string "49228593607874990954666071614777776087"
let privatekey = big_int_from_string "60245260967214266009141128892124363925"

(* This function always generates valid plaintext ballot *)
let valid_ballot n =
    let barr = Array.make_matrix n n 0 in
    Random.self_init ();
    for i = 0 to (n - 1) do 
        for j = i to (n - 1) do 
                barr.(i).(j) <- Random.int 2;
                barr.(j).(i) <- -1 * barr.(i).(j)   
        done 
    done;
    for i = 0 to (n - 1) do
            barr.(i).(i) <- 0;
    done;
    Array.map Array.to_list barr |> Array.to_list 
    |> List.concat |> List.map string_of_int 
  

let invalid_ballot n =
    let barr = Array.make_matrix n n 0 in
    Random.self_init ();
    for i = 0 to (n - 1) do
        for j = i to (n - 1) do
                barr.(i).(j) <- Random.int 100;
                barr.(j).(i) <- Random.int 100  
        done
    done;
    Array.map Array.to_list barr |> Array.to_list  
    |> List.concat |> List.map string_of_int
 

let l =  ["A"; "B"; "C"]
let pair_cand l = Derivation.cross_prod_orig l


let rec print_ballot b = 
  match b with 
  | [] -> ""
  | [((c1, c2), (v1, v2))] -> "("  ^ c1 ^ ", " ^ c2 ^ ", (" ^ Big.to_string v1 ^ ", " ^ Big.to_string v2 ^ "))"
  | ((c1, c2), (v1, v2)) :: tl -> 
       "(" ^ c1 ^ ", " ^ c2 ^ ", (" ^ Big.to_string v1 ^ ", " ^ Big.to_string v2 ^ ")); " ^ print_ballot tl

let gen_ballot vl =
   let bl = List.map (fun x -> encrypt_message (Lib.Group (prime, generator, publickey)) (Big.of_string x)) vl in
   let comb = List.combine (pair_cand l) bl in 
   print_ballot comb 
  
let gen_n_ballots n = 
    for i = 1 to n do 
       print_endline (gen_ballot (valid_ballot (List.length l)));
       print_endline (gen_ballot (invalid_ballot (List.length l)))
    done

let () = 
  gen_n_ballots (int_of_string (Sys.argv.(1)))




