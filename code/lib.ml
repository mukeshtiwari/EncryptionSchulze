
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type bool =
| True
| False

type nat =
| O
| S of nat

type ('a, 'b) sum =
| Inl of 'a
| Inr of 'b

type ('a, 'b) prod =
| Pair of 'a * 'b

(** val fst : ('a1, 'a2) prod -> 'a1 **)

let fst = function
| Pair (x, _) -> x

(** val snd : ('a1, 'a2) prod -> 'a2 **)

let snd = function
| Pair (_, y) -> y

type 'a list =
| Nil
| Cons of 'a * 'a list

(** val length : 'a1 list -> nat **)

let rec length = function
| Nil -> O
| Cons (_, l') -> S (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m0 =
  match l with
  | Nil -> m0
  | Cons (a, l1) -> Cons (a, (app l1 m0))

type comparison =
| Eq
| Lt
| Gt

(** val compOpp : comparison -> comparison **)

let compOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

type ('a, 'p) sigT =
| ExistT of 'a * 'p

type sumbool =
| Left
| Right

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos =
 struct
  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> compare_cont r p q
       | XO q -> compare_cont Gt p q
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q -> compare_cont Lt p q
       | XO q -> compare_cont r p q
       | XH -> Gt)
    | XH -> (match y with
             | XH -> r
             | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq

  (** val eq_dec : positive -> positive -> sumbool **)

  let rec eq_dec p x0 =
    match p with
    | XI p0 -> (match x0 with
                | XI p1 -> eq_dec p0 p1
                | _ -> Right)
    | XO p0 -> (match x0 with
                | XO p1 -> eq_dec p0 p1
                | _ -> Right)
    | XH -> (match x0 with
             | XH -> Left
             | _ -> Right)
 end

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| Nil -> Nil
| Cons (a, t) -> Cons ((f a), (map f t))

(** val forallb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec forallb f = function
| Nil -> True
| Cons (a, l0) -> (match f a with
                   | True -> forallb f l0
                   | False -> False)

module Z =
 struct
  (** val compare : z -> z -> comparison **)

  let compare x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> Eq
             | Zpos _ -> Lt
             | Zneg _ -> Gt)
    | Zpos x' -> (match y with
                  | Zpos y' -> Pos.compare x' y'
                  | _ -> Gt)
    | Zneg x' ->
      (match y with
       | Zneg y' -> compOpp (Pos.compare x' y')
       | _ -> Lt)

  (** val leb : z -> z -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> False
    | _ -> True

  (** val ltb : z -> z -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> True
    | _ -> False

  (** val max : z -> z -> z **)

  let max n m0 =
    match compare n m0 with
    | Lt -> m0
    | _ -> n

  (** val min : z -> z -> z **)

  let min n m0 =
    match compare n m0 with
    | Gt -> m0
    | _ -> n

  (** val eq_dec : z -> z -> sumbool **)

  let eq_dec x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> Left
             | _ -> Right)
    | Zpos x0 -> (match y with
                  | Zpos p0 -> Pos.eq_dec x0 p0
                  | _ -> Right)
    | Zneg x0 -> (match y with
                  | Zneg p0 -> Pos.eq_dec x0 p0
                  | _ -> Right)
 end

(** val bool_of_sumbool : sumbool -> bool **)

let bool_of_sumbool = function
| Left -> True
| Right -> False

(** val z_lt_dec : z -> z -> sumbool **)

let z_lt_dec x y =
  match Z.compare x y with
  | Lt -> Left
  | _ -> Right

(** val z_ge_dec : z -> z -> sumbool **)

let z_ge_dec x y =
  match Z.compare x y with
  | Lt -> Right
  | _ -> Left

(** val z_lt_ge_dec : z -> z -> sumbool **)

let z_lt_ge_dec =
  z_lt_dec

(** val z_ge_lt_dec : z -> z -> sumbool **)

let z_ge_lt_dec =
  z_ge_dec

(** val z_lt_ge_bool : z -> z -> bool **)

let z_lt_ge_bool x y =
  bool_of_sumbool (z_lt_ge_dec x y)

(** val all_pairs : 'a1 list -> ('a1, 'a1) prod list **)

let rec all_pairs = function
| Nil -> Nil
| Cons (c, cs) ->
  Cons ((Pair (c, c)),
    (app (all_pairs cs)
      (app (map (fun x -> Pair (c, x)) cs) (map (fun x -> Pair (x, c)) cs))))

(** val maxlist : z list -> z **)

let rec maxlist = function
| Nil -> Z0
| Cons (h, t) -> (match t with
                  | Nil -> h
                  | Cons (_, _) -> Z.max h (maxlist t))

(** val max_of_nonempty_list_type :
    'a1 list -> ('a1 -> 'a1 -> sumbool) -> z -> ('a1 -> z) -> ('a1, __) sigT **)

let max_of_nonempty_list_type l h1 s f =
  let rec f0 l0 h2 s0 f1 =
    match l0 with
    | Nil -> assert false (* absurd case *)
    | Cons (h, t) ->
      (match t with
       | Nil -> (fun _ -> ExistT (h, __))
       | Cons (h3, t1) ->
         let hmax = z_ge_lt_dec (f1 h) (maxlist (map f1 (Cons (h3, t1)))) in
         (fun _ ->
         match hmax with
         | Left -> ExistT (h, __)
         | Right ->
           let f2 = f0 t h2 s0 f1 __ in
           let ExistT (x, _) = f2 in ExistT (x, __)))
  in f0 l h1 s f __

(** val transitive_dec_first :
    ('a1 -> 'a1 -> sumbool) -> ('a1 -> 'a1 -> sumbool) -> 'a1 -> 'a1 -> 'a1
    -> sumbool **)

let transitive_dec_first _ hp x y z0 =
  let s = hp x y in
  (match s with
   | Left ->
     let s0 = hp y z0 in (match s0 with
                          | Left -> hp x z0
                          | Right -> Left)
   | Right -> Left)

(** val transitive_dec_second :
    ('a1 -> 'a1 -> sumbool) -> ('a1 -> 'a1 -> sumbool) -> 'a1 -> 'a1 -> 'a1
    list -> sumbool **)

let rec transitive_dec_second hcd hp x y = function
| Nil -> Left
| Cons (y0, l0) ->
  (match transitive_dec_second hcd hp x y l0 with
   | Left -> transitive_dec_first hcd hp x y y0
   | Right -> Right)

(** val transitive_dec_third :
    ('a1 -> 'a1 -> sumbool) -> ('a1 -> 'a1 -> sumbool) -> 'a1 -> 'a1 list ->
    'a1 list -> sumbool **)

let rec transitive_dec_third hcd hp x l1 l2 =
  match l1 with
  | Nil -> Left
  | Cons (y, l) ->
    (match transitive_dec_third hcd hp x l l2 with
     | Left -> transitive_dec_second hcd hp x y l2
     | Right -> Right)

(** val transitive_dec_fourth :
    ('a1 -> 'a1 -> sumbool) -> ('a1 -> 'a1 -> sumbool) -> 'a1 list -> 'a1
    list -> 'a1 list -> sumbool **)

let rec transitive_dec_fourth hcd hp l1 l2 l3 =
  match l1 with
  | Nil -> Left
  | Cons (y, l) ->
    (match transitive_dec_fourth hcd hp l l2 l3 with
     | Left -> transitive_dec_third hcd hp y l2 l3
     | Right -> Right)

(** val transitive_dec :
    ('a1 -> 'a1 -> sumbool) -> ('a1 -> 'a1 -> sumbool) -> 'a1 list -> sumbool **)

let transitive_dec hcd hp l =
  transitive_dec_fourth hcd hp l l l

type 'a finite = ('a list, __) sigT

(** val phi_one_helper : ('a1 -> 'a1 -> sumbool) -> 'a1 -> 'a1 -> sumbool **)

let phi_one_helper pdec x a =
  let s = pdec x a in
  (match s with
   | Left ->
     let s0 = pdec a x in (match s0 with
                           | Left -> Right
                           | Right -> Left)
   | Right -> pdec a x)

(** val phi_two_helper :
    ('a1 -> 'a1 -> sumbool) -> 'a1 -> 'a1 -> 'a1 -> (__, __) sum **)

let phi_two_helper pdec a x a0' =
  let s = pdec a x in
  (match s with
   | Left ->
     let s0 = pdec a0' x in
     (match s0 with
      | Left ->
        let s1 = pdec x a in
        (match s1 with
         | Left ->
           let s2 = pdec x a0' in
           (match s2 with
            | Left -> Inl __
            | Right -> Inr __)
         | Right ->
           let s2 = pdec x a0' in
           (match s2 with
            | Left -> Inr __
            | Right -> Inl __))
      | Right -> Inr __)
   | Right ->
     let s0 = pdec a0' x in
     (match s0 with
      | Left -> Inr __
      | Right ->
        let s1 = pdec x a in
        (match s1 with
         | Left ->
           let s2 = pdec x a0' in
           (match s2 with
            | Left -> Inl __
            | Right -> Inr __)
         | Right ->
           let s2 = pdec x a0' in
           (match s2 with
            | Left -> Inr __
            | Right -> Inl __))))

(** val phi_two_inhanced :
    ('a1 -> 'a1 -> sumbool) -> 'a1 -> 'a1 list -> 'a1 -> (__, __) sum **)

let rec phi_two_inhanced pdec a l a0' =
  match l with
  | Nil -> Inl __
  | Cons (y, l0) ->
    (match phi_two_inhanced pdec a l0 a0' with
     | Inl _ ->
       let s = phi_two_helper pdec a y a0' in
       (match s with
        | Inl _ -> Inl __
        | Inr _ -> Inr __)
     | Inr _ -> Inr __)

(** val phi_one_dec :
    ('a1 -> 'a1 -> sumbool) -> 'a1 -> 'a1 list -> sumbool **)

let rec phi_one_dec pdec a = function
| Nil -> Left
| Cons (y, l0) ->
  (match phi_one_dec pdec a l0 with
   | Left -> phi_one_helper pdec y a
   | Right -> Right)

(** val phi_two_dec :
    ('a1 -> 'a1 -> sumbool) -> 'a1 -> 'a1 list -> 'a1 list -> sumbool **)

let rec phi_two_dec pdec a l1 l2 =
  match l1 with
  | Nil -> Right
  | Cons (y, l) ->
    (match phi_two_dec pdec a l l2 with
     | Left -> Left
     | Right ->
       let s = phi_two_inhanced pdec a l2 y in
       (match s with
        | Inl _ -> Left
        | Inr _ -> Right))

(** val phi_decidable :
    ('a1 -> 'a1 -> sumbool) -> 'a1 -> 'a1 list -> sumbool **)

let phi_decidable pdec a l =
  let s = phi_two_dec pdec a l l in
  (match s with
   | Left -> Left
   | Right -> phi_one_dec pdec a l)

(** val vl_or_notvl :
    ('a1 -> 'a1 -> sumbool) -> ('a1 -> 'a1 -> sumbool) -> 'a1 list -> (__,
    __) sum **)

let rec vl_or_notvl adec pdec = function
| Nil -> Inl __
| Cons (y, l0) ->
  (match vl_or_notvl adec pdec l0 with
   | Inl _ ->
     let h0 = pdec y y in
     (match h0 with
      | Left -> Inr __
      | Right ->
        let h1 = transitive_dec adec pdec (Cons (y, l0)) in
        (match h1 with
         | Left ->
           let h2 = phi_decidable pdec y l0 in
           (match h2 with
            | Left -> Inl __
            | Right -> Inr __)
         | Right -> Inr __))
   | Inr _ -> Inr __)

(** val decidable_valid :
    ('a1 -> 'a1 -> sumbool) -> ('a1 -> 'a1 -> sumbool) -> 'a1 finite ->
    sumbool **)

let decidable_valid adec pdec = function
| ExistT (l, _) ->
  let h0 = vl_or_notvl adec pdec l in
  (match h0 with
   | Inl _ -> Left
   | Inr _ -> Right)

type 'cand pathT =
| UnitT of 'cand * 'cand
| ConsT of 'cand * 'cand * 'cand * 'cand pathT

type 'cand wins_type =
  'cand -> (z, ('cand pathT, (('cand, 'cand) prod -> bool, __) sigT) prod)
  sigT

type 'cand loses_type =
  (z, ('cand, ('cand pathT, (('cand, 'cand) prod -> bool, __) sigT) prod)
  sigT) sigT

(** val listify :
    'a1 list -> ('a1 -> 'a1 -> z) -> (('a1, 'a1) prod, z) prod list **)

let listify cand_all0 m0 =
  map (fun s -> Pair ((Pair ((fst s), (snd s))), (m0 (fst s) (snd s))))
    (all_pairs cand_all0)

(** val linear_search :
    ('a1 -> 'a1 -> sumbool) -> ('a1 -> 'a1 -> z) -> 'a1 -> 'a1 -> (('a1, 'a1)
    prod, z) prod list -> z **)

let rec linear_search dec_cand marg c d = function
| Nil -> marg c d
| Cons (y, t) ->
  let Pair (y0, k) = y in
  let Pair (c1, c2) = y0 in
  (match dec_cand c c1 with
   | Left ->
     (match dec_cand d c2 with
      | Left -> k
      | Right -> linear_search dec_cand marg c d t)
   | Right -> linear_search dec_cand marg c d t)

(** val mM :
    'a1 list -> ('a1 -> 'a1 -> sumbool) -> ('a1 -> 'a1 -> z) -> nat -> (('a1,
    'a1) prod, z) prod list **)

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
    'a1 list -> ('a1 -> 'a1 -> sumbool) -> ('a1 -> 'a1 -> z) -> nat -> 'a1 ->
    'a1 -> z **)

let m cand_all0 dec_cand marg n =
  let l = mM cand_all0 dec_cand marg n in
  (fun c d -> linear_search dec_cand marg c d l)

(** val iterated_marg_patht :
    'a1 list -> ('a1 -> 'a1 -> sumbool) -> ('a1 -> 'a1 -> z) -> nat -> z ->
    'a1 -> 'a1 -> 'a1 pathT **)

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
    'a1 list -> ('a1 -> 'a1 -> sumbool) -> ('a1 -> 'a1 -> z) -> 'a1 -> bool **)

let c_wins cand_all0 dec_cand marg c =
  forallb (fun d ->
    Z.leb (m cand_all0 dec_cand marg (length cand_all0) d c)
      (m cand_all0 dec_cand marg (length cand_all0) c d)) cand_all0

(** val iterated_marg_wins_type :
    'a1 list -> ('a1 -> 'a1 -> sumbool) -> ('a1 -> 'a1 -> z) -> 'a1 -> 'a1
    wins_type **)

let iterated_marg_wins_type cand_all0 dec_cand marg c d =
  let s = m cand_all0 dec_cand marg (length cand_all0) c d in
  ExistT (s,
  (let hi =
     iterated_marg_patht cand_all0 dec_cand marg (length cand_all0) s c d
   in
   Pair (hi,
   (let r = m cand_all0 dec_cand marg (length cand_all0) d c in
    ExistT ((fun x ->
    Z.leb (m cand_all0 dec_cand marg (length cand_all0) (fst x) (snd x)) r),
    __)))))

(** val exists_fin_reify : ('a1 -> sumbool) -> 'a1 list -> ('a1, __) sigT **)

let rec exists_fin_reify pdec = function
| Nil -> assert false (* absurd case *)
| Cons (h, t) ->
  (match pdec h with
   | Left -> ExistT (h, __)
   | Right -> exists_fin_reify pdec t)

(** val reify_opponent :
    'a1 list -> ('a1 -> 'a1 -> sumbool) -> ('a1 -> 'a1 -> z) -> 'a1 -> ('a1,
    __) sigT **)

let reify_opponent cand_all0 dec_cand marg c =
  let hdec = fun d ->
    let s =
      z_lt_ge_bool (m cand_all0 dec_cand marg (length cand_all0) c d)
        (m cand_all0 dec_cand marg (length cand_all0) d c)
    in
    (match s with
     | True -> Left
     | False -> Right)
  in
  exists_fin_reify hdec cand_all0

(** val iterated_marg_loses_type :
    'a1 list -> ('a1 -> 'a1 -> sumbool) -> ('a1 -> 'a1 -> z) -> 'a1 -> 'a1
    loses_type **)

let iterated_marg_loses_type cand_all0 dec_cand marg c =
  let hE = reify_opponent cand_all0 dec_cand marg c in
  let ExistT (d, _) = hE in
  let s = m cand_all0 dec_cand marg (length cand_all0) d c in
  ExistT (s, (ExistT (d, (Pair
  ((iterated_marg_patht cand_all0 dec_cand marg (length cand_all0) s d c),
  (ExistT ((fun x ->
  Z.ltb (m cand_all0 dec_cand marg (length cand_all0) (fst x) (snd x)) s),
  __)))))))

(** val wins_loses_type_dec :
    'a1 list -> ('a1 -> 'a1 -> sumbool) -> ('a1 -> 'a1 -> z) -> 'a1 -> ('a1
    wins_type, 'a1 loses_type) sum **)

let wins_loses_type_dec cand_all0 dec_cand marg c =
  let b = c_wins cand_all0 dec_cand marg c in
  (match b with
   | True -> Inl (iterated_marg_wins_type cand_all0 dec_cand marg c)
   | False -> Inr (iterated_marg_loses_type cand_all0 dec_cand marg c))

type plaintext = z

type ciphertext = (z, z) prod

type 'cand ballot = 'cand -> 'cand -> plaintext

type 'cand eballot = 'cand -> 'cand -> ciphertext

type pubkey (* AXIOM TO BE REALIZED *)

type prikey (* AXIOM TO BE REALIZED *)

(** val privatekey : prikey **)

let privatekey =
  failwith "AXIOM TO BE REALIZED"

(** val publickey : pubkey **)

let publickey =
  failwith "AXIOM TO BE REALIZED"

(** val encrypt_ballot : pubkey -> 'a1 ballot -> 'a1 eballot **)

let encrypt_ballot =
  failwith "AXIOM TO BE REALIZED"

(** val decrypt_ballot : prikey -> 'a1 eballot -> 'a1 ballot **)

let decrypt_ballot =
  failwith "AXIOM TO BE REALIZED"

(** val permute_encrypted_ballot : 'a1 eballot -> ('a1 eballot, z) prod **)

let permute_encrypted_ballot =
  failwith "AXIOM TO BE REALIZED"

(** val homomorphic_add_eballots :
    ('a1 -> 'a1 -> ciphertext) -> 'a1 eballot -> 'a1 -> 'a1 -> ciphertext **)

let homomorphic_add_eballots =
  failwith "AXIOM TO BE REALIZED"

type 'cand hCount =
| Ax of 'cand eballot list * ('cand -> 'cand -> ciphertext) * z
| Cvalid of 'cand eballot * 'cand eballot * ('cand -> 'cand -> z) * z * 
   z * 'cand eballot list * ('cand -> 'cand -> ciphertext)
   * ('cand -> 'cand -> ciphertext) * 'cand eballot list * 'cand hCount
| Cinvalid of 'cand eballot * 'cand eballot * ('cand -> 'cand -> z) * 
   z * z * 'cand eballot list * ('cand -> 'cand -> ciphertext)
   * 'cand eballot list * 'cand hCount
| Cdecrypt of 'cand eballot list * ('cand -> 'cand -> ciphertext)
   * ('cand -> 'cand -> plaintext) * z * 'cand hCount
| Fin of ('cand -> 'cand -> z) * ('cand -> bool)
   * ('cand -> ('cand wins_type, 'cand loses_type) sum) * 'cand hCount

(** val ballot_valid_dec :
    'a1 list -> ('a1 -> 'a1 -> sumbool) -> 'a1 ballot -> sumbool **)

let ballot_valid_dec cand_all0 dec_cand b =
  let x = decidable_valid dec_cand in
  let ht = fun c d -> Z.eq_dec (b c d) (Zpos XH) in
  x ht (ExistT (cand_all0, __))

(** val partial_count_all_counted :
    'a1 list -> ('a1 -> 'a1 -> sumbool) -> 'a1 eballot list -> 'a1 eballot
    list -> 'a1 eballot list -> ('a1 -> 'a1 -> ciphertext) -> 'a1 hCount ->
    ('a1 eballot list, ('a1 -> 'a1 -> ciphertext, 'a1 hCount) sigT) sigT **)

let rec partial_count_all_counted cand_all0 dec_cand bs ts inbs m0 hc =
  match ts with
  | Nil -> ExistT (inbs, (ExistT (m0, hc)))
  | Cons (u, us) ->
    let p = permute_encrypted_ballot u in
    let Pair (v, zkppermuv) = p in
    let b = decrypt_ballot privatekey v in
    let s = ballot_valid_dec cand_all0 dec_cand b in
    (match s with
     | Left ->
       let nm = homomorphic_add_eballots m0 u in
       partial_count_all_counted cand_all0 dec_cand bs us inbs nm (Cvalid (u,
         v, b, zkppermuv, Z0, us, m0, nm, inbs, hc))
     | Right ->
       partial_count_all_counted cand_all0 dec_cand bs us (Cons (u, inbs)) m0
         (Cinvalid (u, v, b, zkppermuv, Z0, us, m0, inbs, hc)))

(** val all_ballots_counted :
    'a1 list -> ('a1 -> 'a1 -> sumbool) -> 'a1 eballot list -> ('a1 eballot
    list, ('a1 -> 'a1 -> ciphertext, 'a1 hCount) sigT) sigT **)

let all_ballots_counted cand_all0 dec_cand bs =
  let x =
    partial_count_all_counted cand_all0 dec_cand bs bs Nil
      (encrypt_ballot publickey (fun _ _ -> Z0))
  in
  let h = Ax (bs, (encrypt_ballot publickey (fun _ _ -> Z0)), Z0) in x h

(** val decrypt_margin :
    'a1 list -> ('a1 -> 'a1 -> sumbool) -> 'a1 eballot list -> ('a1 -> 'a1 ->
    plaintext, 'a1 hCount) sigT **)

let decrypt_margin cand_all0 dec_cand bs =
  let s = all_ballots_counted cand_all0 dec_cand bs in
  let ExistT (i, s0) = s in
  let ExistT (encm, p) = s0 in
  let x = fun x -> Cdecrypt (i, encm, (decrypt_ballot privatekey encm), Z0, x)
  in
  let x0 = x p in ExistT ((decrypt_ballot privatekey encm), x0)

(** val schulze_winners :
    'a1 list -> ('a1 -> 'a1 -> sumbool) -> 'a1 eballot list -> ('a1 -> bool,
    'a1 hCount) sigT **)

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
  Cons (A, (Cons (B, (Cons (C, Nil)))))

(** val cand_eq_dec : cand -> cand -> sumbool **)

let cand_eq_dec a b =
  match a with
  | A -> (match b with
          | A -> Left
          | _ -> Right)
  | B -> (match b with
          | B -> Left
          | _ -> Right)
  | C -> (match b with
          | C -> Left
          | _ -> Right)

(** val schulze_winners_pf :
    cand eballot list -> (cand -> bool, cand hCount) sigT **)

let schulze_winners_pf =
  schulze_winners cand_all cand_eq_dec
