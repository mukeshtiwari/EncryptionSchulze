
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

(** val z_le_dec : Big.big_int -> Big.big_int -> bool **)

let z_le_dec x y =
  match Z.compare x y with
  | Gt -> false
  | _ -> true

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

let max_of_nonempty_list_type l h1 s0 f =
  let rec f0 l0 h2 s1 f1 =
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
         else let f2 = f0 t h2 s1 f1 __ in
              let ExistT (x, _) = f2 in ExistT (x, __)))
  in f0 l h1 s0 f __

type 'a finite = ('a list, __) sigT

(** val phi_one_helper :
    ('a1 -> 'a1 -> Big.big_int) -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 ->
    bool option) -> 'a1 -> 'a1 -> bool **)

let phi_one_helper _ _ pdec x a =
  let s0 = pdec x a in
  (match s0 with
   | Some s1 ->
     if s1
     then let s2 = pdec a x in (match s2 with
                                | Some _ -> false
                                | None -> true)
     else false
   | None ->
     let s1 = pdec a x in (match s1 with
                           | Some s2 -> s2
                           | None -> false))

(** val phi_two_helper :
    ('a1 -> 'a1 -> Big.big_int) -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 ->
    bool option) -> 'a1 -> 'a1 -> 'a1 -> bool **)

let phi_two_helper _ _ pdec a x a0' =
  let s0 = pdec a x in
  (match s0 with
   | Some s1 ->
     if s1
     then let s2 = pdec a0' x in
          (match s2 with
           | Some s3 ->
             if s3
             then let s4 = pdec x a in
                  (match s4 with
                   | Some s5 ->
                     if s5
                     then let s6 = pdec x a0' in
                          (match s6 with
                           | Some s7 -> s7
                           | None -> false)
                     else let s6 = pdec x a0' in
                          (match s6 with
                           | Some s7 -> if s7 then false else true
                           | None -> false)
                   | None ->
                     let s5 = pdec x a0' in
                     (match s5 with
                      | Some _ -> false
                      | None -> true))
             else false
           | None -> false)
     else let s2 = pdec a0' x in
          (match s2 with
           | Some s3 ->
             if s3
             then false
             else let s4 = pdec x a in
                  (match s4 with
                   | Some s5 ->
                     if s5
                     then let s6 = pdec x a0' in
                          (match s6 with
                           | Some s7 -> s7
                           | None -> false)
                     else let s6 = pdec x a0' in
                          (match s6 with
                           | Some s7 -> if s7 then false else true
                           | None -> false)
                   | None ->
                     let s5 = pdec x a0' in
                     (match s5 with
                      | Some _ -> false
                      | None -> true))
           | None -> false)
   | None ->
     let s1 = pdec a0' x in
     (match s1 with
      | Some _ -> false
      | None ->
        let s2 = pdec x a in
        (match s2 with
         | Some s3 ->
           if s3
           then let s4 = pdec x a0' in
                (match s4 with
                 | Some s5 -> s5
                 | None -> false)
           else let s4 = pdec x a0' in
                (match s4 with
                 | Some s5 -> if s5 then false else true
                 | None -> false)
         | None ->
           let s3 = pdec x a0' in
           (match s3 with
            | Some _ -> false
            | None -> true))))

(** val phi_two_inhanced :
    ('a1 -> 'a1 -> Big.big_int) -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 ->
    bool option) -> 'a1 -> 'a1 list -> 'a1 -> bool **)

let rec phi_two_inhanced p adec pdec a l a0' =
  match l with
  | [] -> true
  | y :: l0 ->
    if phi_two_inhanced p adec pdec a l0 a0'
    then phi_two_helper p adec pdec a y a0'
    else false

(** val phi_one_dec :
    ('a1 -> 'a1 -> Big.big_int) -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 ->
    bool option) -> 'a1 -> 'a1 list -> bool **)

let rec phi_one_dec p adec pdec a = function
| [] -> true
| y :: l0 ->
  if phi_one_dec p adec pdec a l0
  then phi_one_helper p adec pdec y a
  else false

(** val phi_two_dec :
    ('a1 -> 'a1 -> Big.big_int) -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 ->
    bool option) -> 'a1 -> 'a1 list -> 'a1 list -> bool **)

let rec phi_two_dec p adec pdec a l1 l2 =
  match l1 with
  | [] -> false
  | y :: l ->
    if phi_two_dec p adec pdec a l l2
    then true
    else phi_two_inhanced p adec pdec a l2 y

(** val phi_decidable :
    ('a1 -> 'a1 -> Big.big_int) -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 ->
    bool option) -> 'a1 -> 'a1 list -> bool **)

let phi_decidable p adec pdec a l =
  let s0 = phi_two_dec p adec pdec a l l in
  if s0 then true else phi_one_dec p adec pdec a l

(** val transitive_dec_first_fn :
    ('a1 -> 'a1 -> Big.big_int) -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 ->
    bool option) -> 'a1 -> 'a1 -> 'a1 -> bool **)

let transitive_dec_first_fn _ _ pdec c d e =
  let s0 = pdec c d in
  (match s0 with
   | Some s1 ->
     if s1
     then let s2 = pdec d e in
          (match s2 with
           | Some _ ->
             let s3 = pdec c e in
             (match s3 with
              | Some s4 -> s4
              | None -> false)
           | None -> true)
     else let s2 = pdec d e in
          (match s2 with
           | Some s3 ->
             if s3
             then let s4 = pdec c e in
                  (match s4 with
                   | Some s5 -> s5
                   | None -> false)
             else let s4 = pdec c e in
                  (match s4 with
                   | Some s5 -> if s5 then false else true
                   | None -> false)
           | None ->
             let s3 = pdec c e in
             (match s3 with
              | Some _ -> false
              | None -> true))
   | None ->
     let s1 = pdec d e in
     (match s1 with
      | Some s2 ->
        if s2
        then true
        else let s3 = pdec c e in
             (match s3 with
              | Some _ -> false
              | None -> true)
      | None ->
        let s2 = pdec c e in (match s2 with
                              | Some _ -> false
                              | None -> true)))

(** val transitive_dec_second_fn :
    ('a1 -> 'a1 -> Big.big_int) -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 ->
    bool option) -> 'a1 -> 'a1 -> 'a1 list -> bool **)

let rec transitive_dec_second_fn p adec pdec c d = function
| [] -> true
| y :: l0 ->
  if transitive_dec_second_fn p adec pdec c d l0
  then transitive_dec_first_fn p adec pdec c d y
  else false

(** val transitive_dec_third_fn :
    ('a1 -> 'a1 -> Big.big_int) -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 ->
    bool option) -> 'a1 -> 'a1 list -> 'a1 list -> bool **)

let rec transitive_dec_third_fn p adec pdec c l1 l2 =
  match l1 with
  | [] -> true
  | y :: l ->
    if transitive_dec_third_fn p adec pdec c l l2
    then transitive_dec_second_fn p adec pdec c y l2
    else false

(** val transitive_dec_fourth_fn :
    ('a1 -> 'a1 -> Big.big_int) -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 ->
    bool option) -> 'a1 list -> 'a1 list -> 'a1 list -> bool **)

let rec transitive_dec_fourth_fn p adec pdec l1 l2 l3 =
  match l1 with
  | [] -> true
  | y :: l ->
    if transitive_dec_fourth_fn p adec pdec l l2 l3
    then transitive_dec_third_fn p adec pdec y l2 l3
    else false

(** val transitive_dec_fn :
    ('a1 -> 'a1 -> Big.big_int) -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 ->
    bool option) -> 'a1 list -> bool **)

let transitive_dec_fn p adec pdec l =
  transitive_dec_fourth_fn p adec pdec l l l

(** val vl_or_notvl :
    ('a1 -> 'a1 -> Big.big_int) -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 ->
    bool option) -> 'a1 list -> (__, __) sum **)

let rec vl_or_notvl p adec pdec = function
| [] -> Inl __
| y :: l0 ->
  (match vl_or_notvl p adec pdec l0 with
   | Inl _ ->
     let h0 = pdec y y in
     (match h0 with
      | Some s0 ->
        if s0
        then Inr __
        else let h1 = transitive_dec_fn p adec pdec (y :: l0) in
             if h1
             then let h2 = phi_decidable p adec pdec y l0 in
                  if h2 then Inl __ else Inr __
             else Inr __
      | None -> Inr __)
   | Inr _ -> Inr __)

(** val decidable_valid :
    ('a1 -> 'a1 -> Big.big_int) -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 ->
    bool option) -> 'a1 finite -> bool **)

let decidable_valid p adec pdec = function
| ExistT (l, _) ->
  let h0 = vl_or_notvl p adec pdec l in
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
  map (fun s0 -> (((fst s0), (snd s0)), (m0 (fst s0) (snd s0))))
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

let rec iterated_marg_patht cand_all0 dec_cand marg n s0 c d =
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
         max_of_nonempty_list_type cand_all0 dec_cand s0 (fun x ->
           Z.min (marg c x)
             (linear_search dec_cand marg x d (mM cand_all0 dec_cand marg n0)))
       in
       let ExistT (x, _) = h in
       let iHn = iterated_marg_patht cand_all0 dec_cand marg n0 s0 x d in
       ConsT (c, x, d, iHn)
     | _ -> iterated_marg_patht cand_all0 dec_cand marg n0 s0 c d)

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
  let s0 = m cand_all0 dec_cand marg (length cand_all0) c d in
  ExistT (s0,
  (let hi =
     iterated_marg_patht cand_all0 dec_cand marg (length cand_all0) s0 c d
   in
   (hi,
   (let r0 = m cand_all0 dec_cand marg (length cand_all0) d c in
    ExistT ((fun x ->
    Z.leb (m cand_all0 dec_cand marg (length cand_all0) (fst x) (snd x)) r0),
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
    let s0 =
      z_lt_ge_bool (m cand_all0 dec_cand marg (length cand_all0) c d)
        (m cand_all0 dec_cand marg (length cand_all0) d c)
    in
    if s0 then true else false
  in
  exists_fin_reify hdec cand_all0

(** val iterated_marg_loses_type :
    'a1 list -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> Big.big_int) -> 'a1 ->
    'a1 loses_type **)

let iterated_marg_loses_type cand_all0 dec_cand marg c =
  let hE = reify_opponent cand_all0 dec_cand marg c in
  let ExistT (d, _) = hE in
  let s0 = m cand_all0 dec_cand marg (length cand_all0) d c in
  ExistT (s0, (ExistT (d,
  ((iterated_marg_patht cand_all0 dec_cand marg (length cand_all0) s0 d c),
  (ExistT ((fun x ->
  Z.ltb (m cand_all0 dec_cand marg (length cand_all0) (fst x) (snd x)) s0),
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

type prime (* AXIOM TO BE REALIZED *)

type generator (* AXIOM TO BE REALIZED *)

type pubkey (* AXIOM TO BE REALIZED *)

type prikey (* AXIOM TO BE REALIZED *)

(** val privatekey : prikey **)

let privatekey =
  failwith "AXIOM TO BE REALIZED"

type group =
| Group of prime * generator * pubkey

(** val encrypt_message : group -> plaintext -> ciphertext **)

let encrypt_message =
  failwith "AXIOM TO BE REALIZED"

(** val decrypt_message : group -> prikey -> ciphertext -> plaintext **)

let decrypt_message =
  failwith "AXIOM TO BE REALIZED"

(** val construct_zero_knowledge_decryption_proof :
    group -> prikey -> ciphertext -> char list **)

let construct_zero_knowledge_decryption_proof =
  failwith "AXIOM TO BE REALIZED"

type 'cand permutation = ('cand -> 'cand, __) sigT

type commitment (* AXIOM TO BE REALIZED *)

type zKP (* AXIOM TO BE REALIZED *)

type s (* AXIOM TO BE REALIZED *)

(** val generatePermutation : group -> nat -> 'a1 permutation **)

let generatePermutation =
  failwith "AXIOM TO BE REALIZED"

(** val generateS : group -> nat -> s **)

let generateS =
  failwith "AXIOM TO BE REALIZED"

(** val generatePermutationCommitment :
    group -> nat -> 'a1 permutation -> s -> commitment **)

let generatePermutationCommitment =
  failwith "AXIOM TO BE REALIZED"

(** val zkpPermutationCommitment :
    group -> nat -> 'a1 permutation -> commitment -> s -> zKP **)

let zkpPermutationCommitment =
  failwith "AXIOM TO BE REALIZED"

(** val homomorphic_addition :
    group -> ciphertext -> ciphertext -> ciphertext **)

let homomorphic_addition =
  failwith "AXIOM TO BE REALIZED"

type r (* AXIOM TO BE REALIZED *)

(** val generateR : group -> nat -> r **)

let generateR =
  failwith "AXIOM TO BE REALIZED"

(** val shuffle :
    group -> nat -> ('a1 -> ciphertext) -> 'a1 permutation -> r -> 'a1 ->
    ciphertext **)

let shuffle =
  failwith "AXIOM TO BE REALIZED"

(** val shuffle_zkp :
    group -> nat -> ('a1 -> ciphertext) -> ('a1 -> ciphertext) -> 'a1
    permutation -> commitment -> s -> r -> zKP **)

let shuffle_zkp =
  failwith "AXIOM TO BE REALIZED"

(** val pair_cand_dec :
    ('a1 -> 'a1 -> bool) -> ('a1 * 'a1) -> ('a1 * 'a1) -> bool **)

let pair_cand_dec dec_cand c d =
  let (c0, c1) = c in
  let (c2, c3) = d in
  let h = dec_cand c0 c2 in let h0 = dec_cand c1 c3 in if h then h0 else false

(** val partition_integer : Big.big_int -> bool option option **)

let partition_integer b =
  let s0 = z_le_dec b (Big.opp (Big.double Big.one)) in
  if s0
  then None
  else let s1 = z_ge_dec b (Big.double Big.one) in
       if s1
       then None
       else Some
              (let s2 = Z.eq_dec b (Big.opp Big.one) in
               if s2
               then Some true
               else let s3 = Z.eq_dec b Big.zero in
                    if s3 then Some false else None)

(** val finite_gen :
    ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> Big.big_int) -> ('a1 * 'a1) list
    -> ('a1 -> 'a1 -> __ -> bool option, __) sum **)

let rec finite_gen dec_cand b = function
| [] -> Inl (fun _ _ _ -> assert false (* absurd case *))
| y :: l0 ->
  (match finite_gen dec_cand b l0 with
   | Inl s0 ->
     let (c1, c2) = y in
     let s1 = partition_integer (b c1 c2) in
     (match s1 with
      | Some s2 ->
        Inl (fun c d _ ->
          let s3 = pair_cand_dec dec_cand (c, d) (c1, c2) in
          if s3 then s2 else s0 c d __)
      | None -> Inr __)
   | Inr _ -> Inr __)

(** val finiteness :
    ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> Big.big_int) -> ('a1 * 'a1) list
    -> ('a1 -> 'a1 -> bool option, __) sum **)

let finiteness dec_cand b l =
  let x = finite_gen dec_cand b l in
  (match x with
   | Inl s0 -> Inl (fun c d -> s0 c d __)
   | Inr _ -> Inr __)

(** val dec_pballot :
    'a1 list -> ('a1 -> 'a1 -> bool) -> 'a1 pballot -> bool **)

let dec_pballot cand_all0 dec_cand p =
  let x = finiteness dec_cand p (all_pairs cand_all0) in
  (match x with
   | Inl _ -> true
   | Inr _ -> false)

(** val pballot_valid_dec :
    'a1 list -> ('a1 -> 'a1 -> bool) -> 'a1 pballot -> bool **)

let pballot_valid_dec cand_all0 dec_cand b =
  let x = decidable_valid b dec_cand in
  let ht = finiteness dec_cand b (all_pairs cand_all0) in
  (match ht with
   | Inl s0 -> x s0 (ExistT (cand_all0, __))
   | Inr _ -> false)

(** val matrix_ballot_valid_dec :
    'a1 list -> ('a1 -> 'a1 -> bool) -> 'a1 pballot -> bool **)

let matrix_ballot_valid_dec cand_all0 dec_cand p =
  let s0 = dec_pballot cand_all0 dec_cand p in
  if s0 then pballot_valid_dec cand_all0 dec_cand p else false

type 'cand eCount =
| Ecax of 'cand eballot list * ('cand -> 'cand -> ciphertext)
   * ('cand -> 'cand -> plaintext) * ('cand -> 'cand -> char list)
| Ecvalid of 'cand eballot * 'cand eballot * 'cand eballot * 'cand pballot
   * ('cand -> zKP) * ('cand -> zKP) * ('cand -> 'cand -> char list)
   * commitment * zKP * 'cand eballot list * ('cand -> 'cand -> ciphertext)
   * ('cand -> 'cand -> ciphertext) * 'cand eballot list * 'cand eCount
| Ecinvalid of 'cand eballot * 'cand eballot * 'cand eballot * 'cand pballot
   * ('cand -> zKP) * ('cand -> zKP) * ('cand -> 'cand -> char list)
   * commitment * zKP * 'cand eballot list * ('cand -> 'cand -> ciphertext)
   * 'cand eballot list * 'cand eCount
| Ecdecrypt of 'cand eballot list * ('cand -> 'cand -> ciphertext)
   * ('cand -> 'cand -> plaintext) * ('cand -> 'cand -> char list)
   * 'cand eCount
| Ecfin of ('cand -> 'cand -> Big.big_int) * ('cand -> bool)
   * ('cand -> ('cand wins_type, 'cand loses_type) sum) * 'cand eCount

(** val ecount_all_ballot :
    'a1 list -> group -> 'a1 eballot list -> ('a1 -> 'a1 -> ciphertext, 'a1
    eCount) sigT **)

let ecount_all_ballot _ grp bs =
  let encm = encrypt_message grp Big.zero in
  ExistT ((fun _ _ -> encm), (Ecax (bs, (fun _ _ -> encm), (fun _ _ ->
  Big.zero), (fun _ _ ->
  construct_zero_knowledge_decryption_proof grp privatekey encm))))

(** val idx_search_list :
    ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> 'a2 list -> 'a2 **)

let rec idx_search_list dec_cand c cl l =
  match cl with
  | [] -> assert false (* absurd case *)
  | c0 :: cs ->
    (match l with
     | [] -> assert false (* absurd case *)
     | a :: t -> if dec_cand c c0 then a else idx_search_list dec_cand c cs t)

(** val ppartial_count_all_counted :
    'a1 list -> ('a1 -> 'a1 -> bool) -> group -> 'a1 eballot list -> 'a1
    eballot list -> 'a1 eballot list -> ('a1 -> 'a1 -> ciphertext) -> 'a1
    eCount -> ('a1 eballot list, ('a1 -> 'a1 -> ciphertext, 'a1 eCount) sigT)
    sigT **)

let rec ppartial_count_all_counted cand_all0 dec_cand grp bs ts inbs m0 he =
  match ts with
  | [] -> ExistT (inbs, (ExistT (m0, he)))
  | y :: l ->
    let pi = generatePermutation grp (length cand_all0) in
    let s0 = generateS grp (length cand_all0) in
    let cpi = generatePermutationCommitment grp (length cand_all0) pi s0 in
    let zkpcpi = zkpPermutationCommitment grp (length cand_all0) pi cpi s0 in
    let rrowlistvalues =
      map (fun _ -> generateR grp (length cand_all0)) cand_all0
    in
    let rrowfunvalues = fun c ->
      idx_search_list dec_cand c cand_all0 rrowlistvalues
    in
    let v = fun c -> shuffle grp (length cand_all0) (y c) pi (rrowfunvalues c)
    in
    let zkppermuv = fun c ->
      shuffle_zkp grp (length cand_all0) (y c) (v c) pi cpi s0
        (rrowfunvalues c)
    in
    let rcollistvalues =
      map (fun _ -> generateR grp (length cand_all0)) cand_all0
    in
    let rcolfunvalues = fun c ->
      idx_search_list dec_cand c cand_all0 rcollistvalues
    in
    let t = fun c ->
      shuffle grp (length cand_all0) (fun d -> v d c) pi (rcolfunvalues c)
    in
    let w = fun c d -> t d c in
    let zkppermvw = fun c ->
      shuffle_zkp grp (length cand_all0) (fun d -> v d c) (fun d -> w d c) pi
        cpi s0 (rcolfunvalues c)
    in
    let b = fun c d -> decrypt_message grp privatekey (w c d) in
    let zkpdecw = fun c d ->
      construct_zero_knowledge_decryption_proof grp privatekey (w c d)
    in
    let s1 = matrix_ballot_valid_dec cand_all0 dec_cand b in
    if s1
    then let nm = fun c d -> homomorphic_addition grp (y c d) (m0 c d) in
         let x = Ecvalid (y, v, w, b, zkppermuv, zkppermvw, zkpdecw, cpi,
           zkpcpi, l, m0, nm, inbs, he)
         in
         ppartial_count_all_counted cand_all0 dec_cand grp bs l inbs nm x
    else let x = Ecinvalid (y, v, w, b, zkppermuv, zkppermvw, zkpdecw, cpi,
           zkpcpi, l, m0, inbs, he)
         in
         ppartial_count_all_counted cand_all0 dec_cand grp bs l (y :: inbs)
           m0 x

(** val pall_ballots_counted :
    'a1 list -> ('a1 -> 'a1 -> bool) -> group -> 'a1 eballot list -> ('a1
    eballot list, ('a1 -> 'a1 -> ciphertext, 'a1 eCount) sigT) sigT **)

let pall_ballots_counted cand_all0 dec_cand grp bs =
  let hs = ecount_all_ballot cand_all0 grp bs in
  let ExistT (encm, heg) = hs in
  ppartial_count_all_counted cand_all0 dec_cand grp bs bs [] encm heg

(** val decrypt_margin :
    'a1 list -> ('a1 -> 'a1 -> bool) -> group -> 'a1 eballot list -> ('a1 ->
    'a1 -> plaintext, 'a1 eCount) sigT **)

let decrypt_margin cand_all0 dec_cand grp bs =
  let hc = pall_ballots_counted cand_all0 dec_cand grp bs in
  let ExistT (i, s0) = hc in
  let ExistT (m0, hcount) = s0 in
  let decm = fun c d -> decrypt_message grp privatekey (m0 c d) in
  let zkpdecm = fun c d ->
    construct_zero_knowledge_decryption_proof grp privatekey (m0 c d)
  in
  ExistT (decm, (Ecdecrypt (i, m0, decm, zkpdecm, hcount)))

(** val pschulze_winners :
    'a1 list -> ('a1 -> 'a1 -> bool) -> group -> 'a1 eballot list -> ('a1 ->
    bool, 'a1 eCount) sigT **)

let pschulze_winners cand_all0 dec_cand grp bs =
  let s0 = decrypt_margin cand_all0 dec_cand grp bs in
  let ExistT (dm, hecount) = s0 in
  ExistT ((c_wins cand_all0 dec_cand dm), (Ecfin (dm,
  (c_wins cand_all0 dec_cand dm),
  (wins_loses_type_dec cand_all0 dec_cand dm), hecount)))

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

(** val eschulze_winners_pf :
    group -> cand eballot list -> (cand -> bool, cand eCount) sigT **)

let eschulze_winners_pf =
  pschulze_winners cand_all cand_eq_dec
