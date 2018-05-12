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
  let encarry = Crypto_java.enc_ballot_wrapper arr (Big_integer.create publickey) in 
  create_list_from_array encarry


(* This function decrypts encrypted ballot *)
let dec_ballot lst privatekey = 
  let arr = create_array_from_list lst in 
  let decarr = Crypto_java.dec_ballot_wrapper arr (Big_integer.create privatekey) in
  create_list_from_array decarr

(* this function is zero knowledge proof of decryption *)
let dec_ballot_zkp lst privatekey = 
  let arr = create_array_from_list lst in
  Crypto_java.dec_ballot_zkp_wrapper arr (Big_integer.create privatekey) 

(* This function calculates row permuted array *)  
let row_perm lst publickey = 
  let arr = create_array_from_list lst in
  let rowpermarray = Crypto_java.row_permutation_wrapper arr (Big_integer.create publickey) in 
  create_list_from_array rowpermarray

(* return the zkp of row permuted array *)
let row_perm_zkp lst publickey = 
  let arr = create_array_from_list lst in
  Crypto_java.row_permutation_zkp_wrapper arr (Big_integer.create publickey) 

(* this function calculates column permuted array *)
let column_perm lst publickey = 
  let arr = create_array_from_list lst in 
  let colpermarray = Crypto_java.column_permutation_wrapper arr (Big_integer.create publickey) in 
  create_list_from_array colpermarray

let column_perm_zkp lst publickey = 
  let arr = create_array_from_list lst in 
  Crypto_java.column_permutation_zkp_wrapper arr (Big_integer.create publickey)

(* this function takes two list of strings (which are basically big integers in string) and returns the sum *)
let homomorphic_addition lst1 lst2 =
  let arr1 = create_array_from_list lst1 in
  let arr2 = create_array_from_list lst2 in
  let arr3 = Crypto_java.enc_ballot_mult_wrapper arr1 arr2 in
  create_list_from_array arr3
  
  
(*
let invalid_ballot = (List.map string_of_int [1;1;1;1;1;1;1;1;1])
let valid_ballot = (List.map string_of_int [0; 1; 1; 0; 0; 1; 0; 0; 0])





let _ = 
 let pkey = Big_integer.create "49228593607874990954666071614777776087" in 
 let skey = Big_integer.create "60245260967214266009141128892124363925" in
 let encvbal = enc_ballot valid_ballot pkey in (* encrypt the ballot *)
 let rperm = row_perm encvbal pkey in (* row shift *)
 let rzkp = row_perm_zkp encvbal pkey in (* zero knowledge proof *)
 let cperm = column_perm rperm pkey in  (* column permutation *)
 let czkp = column_perm_zkp rperm pkey in (* zero knowledge proof *)
 let decbal = dec_ballot cperm skey in (* decrypt the ballot *)
 let dzkp = dec_ballot_zkp cperm skey in  (* zero knowledge proof *)
 print_endline "Plaintext ballot";
 List.iter (fun x -> print_endline x) valid_ballot;
 print_endline "Encrypted ballot";
 List.iter (fun x -> print_endline x) encvbal;
 print_endline "Row Permuted ballot";
 List.iter (fun x -> print_endline x) rperm;
 print_endline "Zero knowledge of row shuffle";
 print_endline rzkp;
 print_endline "Column permuted ballot";
 List.iter (fun x -> print_endline x) cperm;
 print_endline "Zero knowledge proof";
 print_endline czkp;
 print_endline "Decrypted permuted ballot";
 List.iter (fun x -> print_endline x) decbal;
 print_endline "Zeroknowledge proof of honest decryption";
 print_endline dzkp
*)


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

let max_of_nonempty_list_type l h1 s f =
  let rec f0 l0 h2 s0 f1 =
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
         else let f2 = f0 t h2 s0 f1 __ in
              let ExistT (x, _) = f2 in ExistT (x, __)))
  in f0 l h1 s f __

(** val transitive_dec_first :
    ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 -> 'a1 -> bool **)

let transitive_dec_first _ hp x y z =
  let s = hp x y in
  if s then let s0 = hp y z in if s0 then hp x z else true else true

(** val transitive_dec_second :
    ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 -> 'a1 list ->
    bool **)

let rec transitive_dec_second hcd hp x y = function
| [] -> true
| y0 :: l0 ->
  if transitive_dec_second hcd hp x y l0
  then transitive_dec_first hcd hp x y y0
  else false

(** val transitive_dec_third :
    ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> 'a1
    list -> bool **)

let rec transitive_dec_third hcd hp x l1 l2 =
  match l1 with
  | [] -> true
  | y :: l ->
    if transitive_dec_third hcd hp x l l2
    then transitive_dec_second hcd hp x y l2
    else false

(** val transitive_dec_fourth :
    ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list ->
    'a1 list -> bool **)

let rec transitive_dec_fourth hcd hp l1 l2 l3 =
  match l1 with
  | [] -> true
  | y :: l ->
    if transitive_dec_fourth hcd hp l l2 l3
    then transitive_dec_third hcd hp y l2 l3
    else false

(** val transitive_dec :
    ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool) -> 'a1 list -> bool **)

let transitive_dec hcd hp l =
  transitive_dec_fourth hcd hp l l l

type 'a finite = ('a list, __) sigT

(** val phi_one_helper : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 -> bool **)

let phi_one_helper pdec x a =
  let s = pdec x a in
  if s then let s0 = pdec a x in if s0 then false else true else pdec a x

(** val phi_two_helper :
    ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 -> 'a1 -> (__, __) sum **)

let phi_two_helper pdec a x a0' =
  let s = pdec a x in
  if s
  then let s0 = pdec a0' x in
       if s0
       then let s1 = pdec x a in
            if s1
            then let s2 = pdec x a0' in if s2 then Inl __ else Inr __
            else let s2 = pdec x a0' in if s2 then Inr __ else Inl __
       else Inr __
  else let s0 = pdec a0' x in
       if s0
       then Inr __
       else let s1 = pdec x a in
            if s1
            then let s2 = pdec x a0' in if s2 then Inl __ else Inr __
            else let s2 = pdec x a0' in if s2 then Inr __ else Inl __

(** val phi_two_inhanced :
    ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> 'a1 -> (__, __) sum **)

let rec phi_two_inhanced pdec a l a0' =
  match l with
  | [] -> Inl __
  | y :: l0 ->
    (match phi_two_inhanced pdec a l0 a0' with
     | Inl _ ->
       let s = phi_two_helper pdec a y a0' in
       (match s with
        | Inl _ -> Inl __
        | Inr _ -> Inr __)
     | Inr _ -> Inr __)

(** val phi_one_dec : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> bool **)

let rec phi_one_dec pdec a = function
| [] -> true
| y :: l0 -> if phi_one_dec pdec a l0 then phi_one_helper pdec y a else false

(** val phi_two_dec :
    ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> 'a1 list -> bool **)

let rec phi_two_dec pdec a l1 l2 =
  match l1 with
  | [] -> false
  | y :: l ->
    if phi_two_dec pdec a l l2
    then true
    else let s = phi_two_inhanced pdec a l2 y in
         (match s with
          | Inl _ -> true
          | Inr _ -> false)

(** val phi_decidable : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> bool **)

let phi_decidable pdec a l =
  let s = phi_two_dec pdec a l l in if s then true else phi_one_dec pdec a l

(** val vl_or_notvl :
    ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool) -> 'a1 list -> (__, __) sum **)

let rec vl_or_notvl adec pdec = function
| [] -> Inl __
| y :: l0 ->
  (match vl_or_notvl adec pdec l0 with
   | Inl _ ->
     let h0 = pdec y y in
     if h0
     then Inr __
     else let h1 = transitive_dec adec pdec (y :: l0) in
          if h1
          then let h2 = phi_decidable pdec y l0 in
               if h2 then Inl __ else Inr __
          else Inr __
   | Inr _ -> Inr __)

(** val decidable_valid :
    ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool) -> 'a1 finite -> bool **)

let decidable_valid adec pdec = function
| ExistT (l, _) ->
  let h0 = vl_or_notvl adec pdec l in
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
  map (fun s -> (((fst s), (snd s)), (m0 (fst s) (snd s))))
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

let rec iterated_marg_patht cand_all0 dec_cand marg n s c d =
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
         max_of_nonempty_list_type cand_all0 dec_cand s (fun x ->
           Z.min (marg c x)
             (linear_search dec_cand marg x d (mM cand_all0 dec_cand marg n0)))
       in
       let ExistT (x, _) = h in
       let iHn = iterated_marg_patht cand_all0 dec_cand marg n0 s x d in
       ConsT (c, x, d, iHn)
     | _ -> iterated_marg_patht cand_all0 dec_cand marg n0 s c d)

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
  let s = m cand_all0 dec_cand marg (length cand_all0) c d in
  ExistT (s,
  (let hi =
     iterated_marg_patht cand_all0 dec_cand marg (length cand_all0) s c d
   in
   (hi,
   (let r = m cand_all0 dec_cand marg (length cand_all0) d c in
    ExistT ((fun x ->
    Z.leb (m cand_all0 dec_cand marg (length cand_all0) (fst x) (snd x)) r),
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
    let s =
      z_lt_ge_bool (m cand_all0 dec_cand marg (length cand_all0) c d)
        (m cand_all0 dec_cand marg (length cand_all0) d c)
    in
    if s then true else false
  in
  exists_fin_reify hdec cand_all0

(** val iterated_marg_loses_type :
    'a1 list -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> Big.big_int) -> 'a1 ->
    'a1 loses_type **)

let iterated_marg_loses_type cand_all0 dec_cand marg c =
  let hE = reify_opponent cand_all0 dec_cand marg c in
  let ExistT (d, _) = hE in
  let s = m cand_all0 dec_cand marg (length cand_all0) d c in
  ExistT (s, (ExistT (d,
  ((iterated_marg_patht cand_all0 dec_cand marg (length cand_all0) s d c),
  (ExistT ((fun x ->
  Z.ltb (m cand_all0 dec_cand marg (length cand_all0) (fst x) (snd x)) s),
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

type pubkey = Big.big_int (* AXIOM TO BE REALIZED *)

type prikey = Big.big_int (* AXIOM TO BE REALIZED *)

(** val privatekey : prikey **)

let privatekey = Big.of_string "60245260967214266009141128892124363925"

(** val publickey : pubkey **)

let publickey = Big.of_string "49228593607874990954666071614777776087"

type cand =
| A
| B
| C

let convert_fun_enc_ballot lstebal =
   match lstebal with
    | [b1; b2; b3; b4; b5; b6; b7; b8; b9; b10; b11; b12; b13; b14; b15; b16; b17; b18] ->
       let f c d = match c, d with
        | A, A -> (Big.of_string b1, Big.of_string b2)
        | A, B -> (Big.of_string b3, Big.of_string b4)
        | A, C -> (Big.of_string b5, Big.of_string b6)
        | B, A -> (Big.of_string b7, Big.of_string b8)
        | B, B -> (Big.of_string b9, Big.of_string b10)
        | B, C -> (Big.of_string b11, Big.of_string b12)
        | C, A -> (Big.of_string b13, Big.of_string b14)
        | C, B -> (Big.of_string b15, Big.of_string b16)
        | C, C -> (Big.of_string b17, Big.of_string b18)
       in f
    | _ -> failwith "something wrong with enc ballot candlist"

let convert_fun_dec_ballot lstbal =
   match lstbal with
    | [b1; b2; b3; b4; b5; b6; b7; b8; b9] ->
       let f c d = match c, d with
        | A, A -> Big.of_string b1
        | A, B -> Big.of_string b2
        | A, C -> Big.of_string b3
        | B, A -> Big.of_string b4
        | B, B -> Big.of_string b5
        | B, C -> Big.of_string b6
        | C, A -> Big.of_string b7
        | C, B -> Big.of_string b8
        | C, C -> Big.of_string b9
       in f
    | _ -> failwith "something wrong with dec ballot candlist"

(** val encrypt_zero_margin :
    'a1 list -> pubkey -> 'a1 pballot -> 'a1 eballot **)

(* don't used ballot, but just construct zero margin ballot *)
let encrypt_zero_margin cand_all pubkey = 
  let paircand = all_pairs cand_all in
  let ballotvalue = List.map (fun (c, d) -> "0") paircand in (* convert the ballot into list of values and change it to string *)
  let zeroencmargin = enc_ballot ballotvalue (Big.to_string pubkey) in
  convert_fun_enc_ballot zeroencmargin   

(** val decrypt_ballot_with_zkp :
    'a1 list -> prikey -> 'a1 eballot -> 'a1 pballot * Big.big_int **)

let rec convert_eballot = function
  | [] -> []
  | (u, v) :: ret -> u :: v :: convert_eballot ret

(* converts string to char list *)
let explode s =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) []

(** val decrypt_ballot_with_zkp :
    'a1 list -> prikey -> 'a1 eballot -> 'a1 ballot * Big.big_int **)
let decrypt_ballot_with_zkp cand_all prikey eballot =
  let paircand = all_pairs cand_all in
  let encballotvalue = List.map (fun (c, d) -> let (u, v) = eballot c d in (Big.to_string u, Big.to_string v)) paircand in
  let decballot = dec_ballot (convert_eballot encballotvalue) (Big.to_string prikey) in 
  let decballotzkp = dec_ballot_zkp (convert_eballot encballotvalue) (Big.to_string prikey) in
  (convert_fun_dec_ballot decballot, explode decballotzkp)
  

(** val row_permute_encrypted_ballot :
    'a1 list -> pubkey -> 'a1 eballot -> 'a1 eballot * Big.big_int **)

let row_permute_encrypted_ballot cand_all pubkey eballot =
  let paircand = all_pairs cand_all in
  let rowpermstr = List.map (fun (c, d) -> let (u, v) = eballot c d in (Big.to_string u, Big.to_string v)) paircand in
  let rowperm = row_perm (convert_eballot rowpermstr) (Big.to_string pubkey) in
  let rowpermzkp = row_perm_zkp (convert_eballot rowpermstr) (Big.to_string pubkey) in
  (convert_fun_enc_ballot rowperm, explode rowpermzkp)

(** val column_permute_encrypted_ballot :
    'a1 list -> pubkey -> 'a1 eballot -> 'a1 eballot * Big.big_int **)

let column_permute_encrypted_ballot cand_all pubkey eballot =
  let paircand = all_pairs cand_all in
  let colpermstr = List.map (fun (c, d) -> let (u, v) = eballot c d in (Big.to_string u, Big.to_string v)) paircand in
  let colperm = column_perm (convert_eballot colpermstr) (Big.to_string pubkey) in
  let colpermzkp = column_perm_zkp (convert_eballot colpermstr) (Big.to_string pubkey) in
  (convert_fun_enc_ballot colperm, explode colpermzkp)

(** val homomorphic_add_eballots :
    'a1 list -> ('a1 -> 'a1 -> ciphertext) -> 'a1 eballot -> 'a1 -> 'a1 ->
    ciphertext **)

let homomorphic_add_eballots cand_all emarg eballot =
  let paircand = all_pairs cand_all in
  let margstr =  List.map (fun (c, d) -> let (u, v) = emarg c d in (Big.to_string u, Big.to_string v)) paircand in
  let ebalstr =  List.map (fun (c, d) -> let (u, v) = eballot c d in (Big.to_string u, Big.to_string v)) paircand in
  let finalstr = homomorphic_addition (convert_eballot margstr) (convert_eballot ebalstr) in
  convert_fun_enc_ballot finalstr


type 'cand hCount =
| Eax of 'cand eballot list * ('cand -> 'cand -> ciphertext)
   * ('cand -> 'cand -> plaintext) * char list
| Ecvalid of 'cand eballot * 'cand eballot * 'cand eballot
   * ('cand -> 'cand -> Big.big_int) * char list * char list * char list
   * 'cand eballot list * ('cand -> 'cand -> ciphertext)
   * ('cand -> 'cand -> ciphertext) * 'cand eballot list * 'cand hCount
| Ecinvalid of 'cand eballot * 'cand eballot * 'cand eballot
   * ('cand -> 'cand -> Big.big_int) * char list * char list * char list
   * 'cand eballot list * ('cand -> 'cand -> ciphertext) * 'cand eballot list
   * 'cand hCount
| Cdecrypt of 'cand eballot list * ('cand -> 'cand -> ciphertext)
   * ('cand -> 'cand -> plaintext) * char list * 'cand hCount
| Efin of ('cand -> 'cand -> Big.big_int) * ('cand -> bool)
   * ('cand -> ('cand wins_type, 'cand loses_type) sum) * 'cand hCount

(** val pballot_valid_dec :
    'a1 list -> ('a1 -> 'a1 -> bool) -> 'a1 pballot -> bool **)

let pballot_valid_dec cand_all0 dec_cand b =
  let x = decidable_valid dec_cand in
  let ht = fun c d -> Z.eq_dec (b c d) Big.one in
  x ht (ExistT (cand_all0, __))

(** val ppartial_count_all_counted :
    'a1 list -> ('a1 -> 'a1 -> bool) -> 'a1 eballot list -> 'a1 eballot list
    -> 'a1 eballot list -> ('a1 -> 'a1 -> ciphertext) -> 'a1 hCount -> ('a1
    eballot list, ('a1 -> 'a1 -> ciphertext, 'a1 hCount) sigT) sigT **)

let rec ppartial_count_all_counted cand_all0 dec_cand bs ts inbs m0 hc =
  match ts with
  | [] -> ExistT (inbs, (ExistT (m0, hc)))
  | u :: us ->
    let p = row_permute_encrypted_ballot cand_all0 publickey u in
    let (v, zkppermuv) = p in
    let p0 = column_permute_encrypted_ballot cand_all0 publickey v in
    let (w, zkppermvw) = p0 in
    let p1 = decrypt_ballot_with_zkp cand_all0 privatekey w in
    let (b, zkphdec) = p1 in
    let s = pballot_valid_dec cand_all0 dec_cand b in
    if s
    then let nm = homomorphic_add_eballots cand_all0 m0 u in
         ppartial_count_all_counted cand_all0 dec_cand bs us inbs nm (Ecvalid
           (u, v, w, b, zkppermuv, zkppermvw, zkphdec, us, m0, nm, inbs, hc))
    else ppartial_count_all_counted cand_all0 dec_cand bs us (u :: inbs) m0
           (Ecinvalid (u, v, w, b, zkppermuv, zkppermvw, zkphdec, us, m0,
           inbs, hc))

(** val pall_ballots_counted :
    'a1 list -> ('a1 -> 'a1 -> bool) -> 'a1 eballot list -> ('a1 eballot
    list, ('a1 -> 'a1 -> ciphertext, 'a1 hCount) sigT) sigT **)

let pall_ballots_counted cand_all0 dec_cand bs =
  let enczmargin = encrypt_zero_margin cand_all0 publickey in
  let p = decrypt_ballot_with_zkp cand_all0 privatekey enczmargin in
  let (decmarg, ezkp) = p in
  let x = ppartial_count_all_counted cand_all0 dec_cand bs bs [] enczmargin in
  let h = Eax (bs, enczmargin, decmarg, ezkp) in x h

(** val decrypt_margin :
    'a1 list -> ('a1 -> 'a1 -> bool) -> 'a1 eballot list -> ('a1 -> 'a1 ->
    plaintext, 'a1 hCount) sigT **)

let decrypt_margin cand_all0 dec_cand bs =
  let s = pall_ballots_counted cand_all0 dec_cand bs in
  let ExistT (i, s0) = s in
  let ExistT (encm, p) = s0 in
  let p0 = decrypt_ballot_with_zkp cand_all0 privatekey encm in
  let (decmarg, dechzkp) = p0 in
  let x = fun x -> Cdecrypt (i, encm, decmarg, dechzkp, x) in
  let x0 = x p in ExistT (decmarg, x0)

(** val pschulze_winners :
    'a1 list -> ('a1 -> 'a1 -> bool) -> 'a1 eballot list -> ('a1 -> bool, 'a1
    hCount) sigT **)

let pschulze_winners cand_all0 dec_cand bs =
  let s = decrypt_margin cand_all0 dec_cand bs in
  let ExistT (dm, h) = s in
  ExistT ((c_wins cand_all0 dec_cand dm), (Efin (dm,
  (c_wins cand_all0 dec_cand dm),
  (wins_loses_type_dec cand_all0 dec_cand dm), h)))
(*
type cand =
| A
| B
| C *)

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

(** val schulze_winners_pf :
    cand eballot list -> (cand -> bool, cand hCount) sigT **)

let schulze_winners_pf =
  pschulze_winners cand_all cand_eq_dec


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



let cl2s cl = String.concat "" (List.map (String.make 1) cl)

let show_count l =
  let rec show_count_aux acc = function 
  | Eax (_, m, dm, v) -> (underline ("M: " ^ show_enc_marg m ^ ", Decrypted margin " ^ show_marg dm ^ ", Zero Knowledge Proof of Honest Decryption: " ^ (cl2s v))) :: acc 
  | Ecvalid (u, v, w, b, zkppermuv, zkppermvw, zkpdecw, us, m, nm, inbs, c) ->
     show_count_aux (underline (
       "V: [" ^ show_enc_ballot u ^ (if bool_b us then "]" else ",..]")  ^
         ", I:  " ^ show_list_inv_ballot inbs  ^ ", M: " ^ show_enc_marg m ^ ", Row Permuted Ballot: " ^ show_enc_ballot v ^
         ", Column Permuted Ballot: " ^ show_enc_ballot w ^
         ", Decryption of Permuted Ballot: " ^ show_ballot b ^ ", Zero Knowledge Proof of Row Permutation: " ^ (cl2s zkppermuv) ^ 
         ", Zero Knowledge Proof of Column Permutation: " ^ (cl2s zkppermvw) ^
         ", Zero Knowledge Proof of Decryption: " ^ (cl2s zkpdecw)) :: acc) c 
  | Ecinvalid (u, v, w, b, zkppermuv, zkppermvw, zkpdecw, us, m, inbs, c)  ->
     show_count_aux (underline (
       "V: [" ^ show_enc_ballot u ^
         (if bool_b us then "]" else ",..]") ^ ", I: " ^ show_list_inv_ballot inbs ^ 
           ", M: " ^ show_enc_marg m ^ ", Row Permuted Ballot: " ^ show_enc_ballot v ^ 
           ", Column Permuted Ballot: " ^ show_enc_ballot w ^
           ", Decryption of Permuted Ballot: " ^ show_ballot b ^ ", Zero Knowledge Proof of Row Permutation: " ^ (cl2s zkppermuv) ^ 
           ", Zero Knowledge Proof of Column Permutation: " ^ (cl2s zkppermvw) ^
           ", Zero Knowledge Proof of Decryption: " ^ (cl2s zkpdecw)) :: acc) c
  | Cdecrypt (inbs, m, dm, zkpdecm, c) -> 
     show_count_aux (underline (
       "V: [], I: " ^ show_list_inv_ballot inbs ^ ", M: " ^ show_enc_marg m ^ ", DM: " ^ show_marg dm ^ 
       ", Zero Knowledge Proof of Decryption: " ^ (cl2s zkpdecm)) :: acc) c 
  | Efin (m, p, f, c) ->
     show_count_aux (underline (
       "DM: " ^ show_marg m ^
       String.concat "\n" (List.map (fun x -> show_cand f x) cand_all) ^ "\n") :: acc) c
  in show_count_aux [] l 



           
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
      in  f
   | _ -> failwith "failed to match pattern" 

                   
let map f l =
  let rec map_aux acc = function
    | [] -> acc []
    | x :: xs -> map_aux (fun ys -> acc (f x :: ys)) xs
  in
  map_aux (fun ys -> ys) l

(*
let fbal = [('A', 'A', ("36298779851590675171784493441809471218", "154402313824196585415782197403965742251")); ('A', 'B', ("143861303906211665855056403061922189147", "8416295835412847971984587159961722280")); ('A', 'C', ("154802215556503296917572828453631007857", "159992136206383694022050707744893109384")); ('B', 'A', ("10082618643668849505327936684527005963", "23507983030617306800838885722953330452")); ('B', 'B', ("112074768704955408044063928805099751409", "101334548041525603500290857389189133621")); ('B', 'C', ("20997879429031352966166576492046928799", "24873500185684887763331722379481691706")); ('C', 'A', ("165341292400026470412885032825699039026", "79093719764332669958326536531596289367")); ('C', 'B', ("68607147314128719103667514144415278841", "83213741986070549122445942673431365894")); ('C', 'C', ("97726566857485399844584900308261246487", "32567851913734176181734306333938927512"))]


let sbal = [('A', 'A', ("72233019768267204190901325348317701512", "62550683788631022500254685291790497145")); ('A', 'B', ("101278468642864358014997944035442827222", "42348323394941099048494706278639673802")); ('A', 'C', ("167982540300220192723644011026727632221", "67417063195893511807550830183724691580")); ('B', 'A', ("137015918377085389910533229116551304362", "6843361110662429817471014779744016136")); ('B', 'B', ("151385763570350315745983636122538421095", "52198379059461106548243108394695535567")); ('B', 'C', ("42311382564617960616391879945513276147", "79480503986134208810191987730395404862")); ('C', 'A', ("38837241630957626554468741266542334082", "117199091050002770483871737779226683680")); ('C', 'B', ("94433157604374082654657839726996858986", "85635479354648785714300946031836499124")); ('C', 'C', ("57790062015352140240629368337806293663", "74538277283805585965681318228709837776"))]
*)
(*
let e = [onebal; onebal; onebal; onebal; onebal; onebal; onebal; onebal; onebal; onebal]
*)

let _ = 
  let e = Parser.prog Lexer.lexeme (Lexing.from_channel stdin) in
  let w = map (fun x -> map (fun (a, b, (c, d)) -> (cc a, cc b,  (Big.of_string c, Big.of_string d))) x) e in
  let v = map (fun x -> balfun x) w in
  Format.printf "%s" "I have printed something";
  match schulze_winners_pf v with
  | ExistT (f, y) ->
     List.iter (fun x -> Format.printf "%s" x) (show_count y)
                    (*                
     List.iter (fun x -> Format.printf "%s\n"  (string_of_bool (f x))) [A; B; C]
          *)                                        
               
  
