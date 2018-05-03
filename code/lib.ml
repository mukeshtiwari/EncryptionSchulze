open Javaocamlbinding

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

type 'cand ballot = 'cand -> 'cand -> plaintext

type 'cand eballot = 'cand -> 'cand -> ciphertext

type pubkey = Big.big_int (* AXIOM TO BE REALIZED *)

type prikey = Big.big_int (* AXIOM TO BE REALIZED *)

(** val privatekey : prikey **)

let privatekey = Big.of_string "60245260967214266009141128892124363925"


(** val publickey : pubkey **)

let publickey = Big.of_string "49228593607874990954666071614777776087"

let convert_fun_enc_ballot paircand lstebal = 
   match paircand,lstebal with
    | [(A, A); (A, B); (A, C); (B, A); (B, B); (B, C); (C, A); (C, B); (C, C)],
      [b1; b2; b3; b4; b5; b6; b7; b8; b9; b10; b11; b12; b13; b14; b15; b16; b17; b18] -> 
      let f c d -> match c, d with
        | A, A -> (Big.of_string b1, Big.of_string b2)
        | A, B -> (Big.of_string b3, Big.of_string b4)
        | A, C -> (Big.of_string b5, Big.of_string b6)
        | B, A -> (Big.of_string b7, Big.of_string b8)
        | B, B -> (Big.of_string b9, Big.of_string b10)
        | B, C -> (Big.of_string b11, Big.of_string b12)
        | C, A -> (Big.of_string b13, Big.of_string b14)
        | C, B -> (Big.of_string b15, Big.of_string b16)
        | C, C -> (Big.of_string b17, Big.of_string b18)
        | _, _ -> failwith "something different candidates"
      in f
    | _, _ -> failwith "something wrong with candlist" 
  

let convert_fun_dec_ballot paircand lstebal = 
   match paircand,lstbal with
    | [(A, A); (A, B); (A, C); (B, A); (B, B); (B, C); (C, A); (C, B); (C, C)], 
      [b1; b2; b3; b4; b5; b6; b7; b8; b9] ->
      let f c d -> match c, d with
        | A, A -> Big.of_string b1
        | A, B -> Big.of_string b2
        | A, C -> Big.of_string b3
        | B, A -> Big.of_string b4
        | B, B -> Big.of_string b5
        | B, C -> Big.of_string b6
        | C, A -> Big.of_string b7
        | C, B -> Big.of_string b8
        | C, C -> Big.of_string b9
        | _, _ -> failwith "something different candidates"
      in f
    | _, _ -> failwith "something wrong with candlist"
   
 
(** val encrypt_zero_margin_with_zkp :
    'a1 list -> pubkey -> 'a1 ballot -> 'a1 eballot * Big.big_int **)

let encrypt_zero_margin_with_zkp cand_all pubkey ballot =
  let paircand = all_pairs cand_all in 
  let ballotvalue = List.map (fun (c, d) -> Bit.to_string (ballot c d)) paircand in (* convert the ballot into list of values and change it to string *)
  let zeroencmargin = Javaocamlbinding.enc_ballot ballotvalue publickey in 
  (convert_fun_enc_ballot pairscand zeroencmargin, Big.zero)
   

(** val decrypt_ballot_with_zkp :
    'a1 list -> prikey -> 'a1 eballot -> 'a1 ballot * Big.big_int **)

let decrypt_ballot_with_zkp cand_all prikey eballot = 
  let paircand = all_pairs cand_all in 
  let encballotval = List.map (fun (c, d) -> let (u, v) = eballot c d in (Big.to_string u, Big.to_string v)) paircand in 
  let decballot = Javaocamlbinding.dec_ballot encballotval prikey  in 
  (convert_fun_dec_ballot paircand decballot, Big.zero)

(** val row_permute_encrypted_ballot :
    'a1 list -> pubkey -> 'a1 eballot -> 'a1 eballot * Big.big_int **)

let row_permute_encrypted_ballot cand_all pubkey eballot = 
  let paircand = all_pairs cand_all in 
  let rowpermstr = List.map (fun (c, d) -> let (u, v) = eballot c d in (Big.to_string u, Big.to_string v)) paircand in 
  let rowperm = Javaocamlbinding.row_perm rowpermstr pubkey in 
  (convert_fun_enc_ballot paircand rowperm, Big.zero)

(** val column_permute_encrypted_ballot :
    'a1 list -> pubkey -> 'a1 eballot -> 'a1 eballot * Big.big_int **)

let column_permute_encrypted_ballot cand_all pubkey eballot = 
  let paircand = all_pairs cand_all in 
  let colpermstr = List.map (fun (c, d) -> let (u, v) = eballot c d in (Big.to_string u, Big.to_string v)) paircand in
  let colperm = Javaocamlbinding.column_perm colpermstr pubkey in 
  (convert_fun_enc_ballot paircand colperm, Big.zero)


(** val homomorphic_add_eballots :
    'a1 list -> ('a1 -> 'a1 -> ciphertext) -> 'a1 eballot -> 'a1 -> 'a1 ->
    ciphertext **)

let homomorphic_add_eballots cand_all emarg eballot = 
  let paircand = all_paris cand_all in 
  let margstr =  List.map (fun (c, d) -> let (u, v) = m c d in (Big.to_string u, Big.to_string v)) paircand in
  let ebalstr =  List.map (fun (c, d) -> let (u, v) = eballot c d in (Big.to_string u, Big.to_string v)) paircand in
  let finalstr = Javaocamlbinding.homomorphic_addition margstr ebalstr in 
  convert_fun_enc_ballot pairscand finalstr

type 'cand hCount =
| Ax of 'cand eballot list * ('cand -> 'cand -> ciphertext) * Big.big_int
| Cvalid of 'cand eballot * 'cand eballot * 'cand eballot
   * ('cand -> 'cand -> Big.big_int) * Big.big_int * Big.big_int
   * Big.big_int * 'cand eballot list * ('cand -> 'cand -> ciphertext)
   * ('cand -> 'cand -> ciphertext) * 'cand eballot list * 'cand hCount
| Cinvalid of 'cand eballot * 'cand eballot * 'cand eballot
   * ('cand -> 'cand -> Big.big_int) * Big.big_int * Big.big_int
   * Big.big_int * 'cand eballot list * ('cand -> 'cand -> ciphertext)
   * 'cand eballot list * 'cand hCount
| Cdecrypt of 'cand eballot list * ('cand -> 'cand -> ciphertext)
   * ('cand -> 'cand -> plaintext) * Big.big_int * 'cand hCount
| Fin of ('cand -> 'cand -> Big.big_int) * ('cand -> bool)
   * ('cand -> ('cand wins_type, 'cand loses_type) sum) * 'cand hCount

(** val ballot_valid_dec :
    'a1 list -> ('a1 -> 'a1 -> bool) -> 'a1 ballot -> bool **)

let ballot_valid_dec cand_all0 dec_cand b =
  let x = decidable_valid dec_cand in
  let ht = fun c d -> Z.eq_dec (b c d) Big.one in
  x ht (ExistT (cand_all0, __))

(** val partial_count_all_counted :
    'a1 list -> ('a1 -> 'a1 -> bool) -> 'a1 eballot list -> 'a1 eballot list
    -> 'a1 eballot list -> ('a1 -> 'a1 -> ciphertext) -> 'a1 hCount -> ('a1
    eballot list, ('a1 -> 'a1 -> ciphertext, 'a1 hCount) sigT) sigT **)

let rec partial_count_all_counted cand_all0 dec_cand bs ts inbs m0 hc =
  match ts with
  | [] -> ExistT (inbs, (ExistT (m0, hc)))
  | u :: us ->
    let p = row_permute_encrypted_ballot cand_all0 publickey u in
    let (v, zkppermuv) = p in
    let p0 = column_permute_encrypted_ballot cand_all0 publickey v in
    let (w, zkppermvw) = p0 in
    let p1 = decrypt_ballot_with_zkp cand_all0 privatekey w in
    let (b, zkphdec) = p1 in
    let s = ballot_valid_dec cand_all0 dec_cand b in
    if s
    then let nm = homomorphic_add_eballots cand_all0 m0 u in
         partial_count_all_counted cand_all0 dec_cand bs us inbs nm (Cvalid
           (u, v, w, b, zkppermuv, zkppermvw, zkphdec, us, m0, nm, inbs, hc))
    else partial_count_all_counted cand_all0 dec_cand bs us (u :: inbs) m0
           (Cinvalid (u, v, w, b, zkppermuv, zkppermvw, zkphdec, us, m0,
           inbs, hc))

(** val all_ballots_counted :
    'a1 list -> ('a1 -> 'a1 -> bool) -> 'a1 eballot list -> ('a1 eballot
    list, ('a1 -> 'a1 -> ciphertext, 'a1 hCount) sigT) sigT **)

let all_ballots_counted cand_all0 dec_cand bs =
  let p =
    encrypt_zero_margin_with_zkp cand_all0 publickey (fun _ _ -> Big.zero)
  in
  let (enczmargin, ezkp) = p in
  let x = partial_count_all_counted cand_all0 dec_cand bs bs [] enczmargin in
  let h = Ax (bs, enczmargin, ezkp) in x h

(** val decrypt_margin :
    'a1 list -> ('a1 -> 'a1 -> bool) -> 'a1 eballot list -> ('a1 -> 'a1 ->
    plaintext, 'a1 hCount) sigT **)

let decrypt_margin cand_all0 dec_cand bs =
  let s = all_ballots_counted cand_all0 dec_cand bs in
  let ExistT (i, s0) = s in
  let ExistT (encm, p) = s0 in
  let p0 = decrypt_ballot_with_zkp cand_all0 privatekey encm in
  let (decmarg, dechzkp) = p0 in
  let x = fun x -> Cdecrypt (i, encm, decmarg, dechzkp, x) in
  let x0 = x p in ExistT (decmarg, x0)

(** val schulze_winners :
    'a1 list -> ('a1 -> 'a1 -> bool) -> 'a1 eballot list -> ('a1 -> bool, 'a1
    hCount) sigT **)

let schulze_winners cand_all0 dec_cand bs =
  let s = decrypt_margin cand_all0 dec_cand bs in
  let ExistT (dm, h) = s in
  ExistT ((c_wins cand_all0 dec_cand dm), (Fin (dm,
  (c_wins cand_all0 dec_cand dm),
  (wins_loses_type_dec cand_all0 dec_cand dm), h)))

type cand =
| A
| B
| C

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
  schulze_winners cand_all cand_eq_dec
