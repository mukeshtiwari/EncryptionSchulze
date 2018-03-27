module Lib where

import qualified Prelude

__ :: any
__ = Prelude.error "Logical or arity value used"

eq_rect :: a1 -> a2 -> a1 -> a2
eq_rect _ f _ =
  f

data Bool =
   True
 | False
 deriving (Prelude.Show)

andb :: Bool -> Bool -> Bool
andb b2 b3 =
  case b2 of {
   True -> b3;
   False -> False}

data Nat =
   O
 | S Nat

nat_rect :: a1 -> (Nat -> a1 -> a1) -> Nat -> a1
nat_rect f f0 n =
  case n of {
   O -> f;
   S n0 -> f0 n0 (nat_rect f f0 n0)}

data Sum a b =
   Inl a
 | Inr b

data Prod a b =
   Pair a b

fst :: (Prod a1 a2) -> a1
fst p =
  case p of {
   Pair x _ -> x}

snd :: (Prod a1 a2) -> a2
snd p =
  case p of {
   Pair _ y -> y}

data List a =
   Nil
 | Cons a (List a)

list_rect :: a2 -> (a1 -> (List a1) -> a2 -> a2) -> (List a1) -> a2
list_rect f f0 l =
  case l of {
   Nil -> f;
   Cons y l0 -> f0 y l0 (list_rect f f0 l0)}

list_rec :: a2 -> (a1 -> (List a1) -> a2 -> a2) -> (List a1) -> a2
list_rec =
  list_rect

length :: (List a1) -> Nat
length l =
  case l of {
   Nil -> O;
   Cons _ l' -> S (length l')}

app :: (List a1) -> (List a1) -> List a1
app l m0 =
  case l of {
   Nil -> m0;
   Cons a l1 -> Cons a (app l1 m0)}

data Comparison =
   Eq
 | Lt
 | Gt

compOpp :: Comparison -> Comparison
compOpp r =
  case r of {
   Eq -> Eq;
   Lt -> Gt;
   Gt -> Lt}

type Sig a =
  a
  -- singleton inductive, whose constructor was exist
  
data SigT a p =
   ExistT a p

data Sumbool =
   Left
 | Right

sumbool_rect :: (() -> a1) -> (() -> a1) -> Sumbool -> a1
sumbool_rect f f0 s =
  case s of {
   Left -> f __;
   Right -> f0 __}

sumbool_rec :: (() -> a1) -> (() -> a1) -> Sumbool -> a1
sumbool_rec =
  sumbool_rect

data Positive =
   XI Positive
 | XO Positive
 | XH

positive_rect :: (Positive -> a1 -> a1) -> (Positive -> a1 -> a1) -> a1 ->
                 Positive -> a1
positive_rect f f0 f1 p =
  case p of {
   XI p0 -> f p0 (positive_rect f f0 f1 p0);
   XO p0 -> f0 p0 (positive_rect f f0 f1 p0);
   XH -> f1}

positive_rec :: (Positive -> a1 -> a1) -> (Positive -> a1 -> a1) -> a1 ->
                Positive -> a1
positive_rec =
  positive_rect

data Z =
   Z0
 | Zpos Positive
 | Zneg Positive

z_rect :: a1 -> (Positive -> a1) -> (Positive -> a1) -> Z -> a1
z_rect f f0 f1 z =
  case z of {
   Z0 -> f;
   Zpos x -> f0 x;
   Zneg x -> f1 x}

z_rec :: a1 -> (Positive -> a1) -> (Positive -> a1) -> Z -> a1
z_rec =
  z_rect

succ :: Positive -> Positive
succ x =
  case x of {
   XI p -> XO (succ p);
   XO p -> XI p;
   XH -> XO XH}

add :: Positive -> Positive -> Positive
add x y =
  case x of {
   XI p ->
    case y of {
     XI q -> XO (add_carry p q);
     XO q -> XI (add p q);
     XH -> XO (succ p)};
   XO p ->
    case y of {
     XI q -> XI (add p q);
     XO q -> XO (add p q);
     XH -> XI p};
   XH ->
    case y of {
     XI q -> XO (succ q);
     XO q -> XI q;
     XH -> XO XH}}

add_carry :: Positive -> Positive -> Positive
add_carry x y =
  case x of {
   XI p ->
    case y of {
     XI q -> XI (add_carry p q);
     XO q -> XO (add_carry p q);
     XH -> XI (succ p)};
   XO p ->
    case y of {
     XI q -> XO (add_carry p q);
     XO q -> XI (add p q);
     XH -> XO (succ p)};
   XH ->
    case y of {
     XI q -> XI (succ q);
     XO q -> XO (succ q);
     XH -> XI XH}}

pred_double :: Positive -> Positive
pred_double x =
  case x of {
   XI p -> XI (XO p);
   XO p -> XI (pred_double p);
   XH -> XH}

compare_cont :: Comparison -> Positive -> Positive -> Comparison
compare_cont r x y =
  case x of {
   XI p ->
    case y of {
     XI q -> compare_cont r p q;
     XO q -> compare_cont Gt p q;
     XH -> Gt};
   XO p ->
    case y of {
     XI q -> compare_cont Lt p q;
     XO q -> compare_cont r p q;
     XH -> Gt};
   XH ->
    case y of {
     XH -> r;
     _ -> Lt}}

compare :: Positive -> Positive -> Comparison
compare =
  compare_cont Eq

eq_dec :: Positive -> Positive -> Sumbool
eq_dec x y =
  positive_rec (\_ h y0 ->
    case y0 of {
     XI p0 -> sumbool_rec (\_ -> Left) (\_ -> Right) (h p0);
     _ -> Right}) (\_ h y0 ->
    case y0 of {
     XO p0 -> sumbool_rec (\_ -> Left) (\_ -> Right) (h p0);
     _ -> Right}) (\y0 ->
    case y0 of {
     XH -> Left;
     _ -> Right}) x y

map :: (a1 -> a2) -> (List a1) -> List a2
map f l =
  case l of {
   Nil -> Nil;
   Cons a t -> Cons (f a) (map f t)}

forallb :: (a1 -> Bool) -> (List a1) -> Bool
forallb f l =
  case l of {
   Nil -> True;
   Cons a l0 -> andb (f a) (forallb f l0)}

double :: Z -> Z
double x =
  case x of {
   Z0 -> Z0;
   Zpos p -> Zpos (XO p);
   Zneg p -> Zneg (XO p)}

succ_double :: Z -> Z
succ_double x =
  case x of {
   Z0 -> Zpos XH;
   Zpos p -> Zpos (XI p);
   Zneg p -> Zneg (pred_double p)}

pred_double0 :: Z -> Z
pred_double0 x =
  case x of {
   Z0 -> Zneg XH;
   Zpos p -> Zpos (pred_double p);
   Zneg p -> Zneg (XI p)}

pos_sub :: Positive -> Positive -> Z
pos_sub x y =
  case x of {
   XI p ->
    case y of {
     XI q -> double (pos_sub p q);
     XO q -> succ_double (pos_sub p q);
     XH -> Zpos (XO p)};
   XO p ->
    case y of {
     XI q -> pred_double0 (pos_sub p q);
     XO q -> double (pos_sub p q);
     XH -> Zpos (pred_double p)};
   XH ->
    case y of {
     XI q -> Zneg (XO q);
     XO q -> Zneg (pred_double q);
     XH -> Z0}}

add0 :: Z -> Z -> Z
add0 x y =
  case x of {
   Z0 -> y;
   Zpos x' ->
    case y of {
     Z0 -> x;
     Zpos y' -> Zpos (add x' y');
     Zneg y' -> pos_sub x' y'};
   Zneg x' ->
    case y of {
     Z0 -> x;
     Zpos y' -> pos_sub y' x';
     Zneg y' -> Zneg (add x' y')}}

compare0 :: Z -> Z -> Comparison
compare0 x y =
  case x of {
   Z0 ->
    case y of {
     Z0 -> Eq;
     Zpos _ -> Lt;
     Zneg _ -> Gt};
   Zpos x' ->
    case y of {
     Zpos y' -> compare x' y';
     _ -> Gt};
   Zneg x' ->
    case y of {
     Zneg y' -> compOpp (compare x' y');
     _ -> Lt}}

leb :: Z -> Z -> Bool
leb x y =
  case compare0 x y of {
   Gt -> False;
   _ -> True}

ltb :: Z -> Z -> Bool
ltb x y =
  case compare0 x y of {
   Lt -> True;
   _ -> False}

max :: Z -> Z -> Z
max n m0 =
  case compare0 n m0 of {
   Lt -> m0;
   _ -> n}

min :: Z -> Z -> Z
min n m0 =
  case compare0 n m0 of {
   Gt -> m0;
   _ -> n}

eq_dec0 :: Z -> Z -> Sumbool
eq_dec0 x y =
  z_rec (\y0 ->
    case y0 of {
     Z0 -> Left;
     _ -> Right}) (\p y0 ->
    case y0 of {
     Zpos p0 -> sumbool_rec (\_ -> Left) (\_ -> Right) (eq_dec p p0);
     _ -> Right}) (\p y0 ->
    case y0 of {
     Zneg p0 -> sumbool_rec (\_ -> Left) (\_ -> Right) (eq_dec p p0);
     _ -> Right}) x y

bool_of_sumbool :: Sumbool -> Bool
bool_of_sumbool h =
  sumbool_rec (\_ -> True) (\_ -> False) h

z_lt_dec :: Z -> Z -> Sumbool
z_lt_dec x y =
  case compare0 x y of {
   Lt -> Left;
   _ -> Right}

z_ge_dec :: Z -> Z -> Sumbool
z_ge_dec x y =
  case compare0 x y of {
   Lt -> Right;
   _ -> Left}

z_lt_ge_dec :: Z -> Z -> Sumbool
z_lt_ge_dec x y =
  z_lt_dec x y

z_ge_lt_dec :: Z -> Z -> Sumbool
z_ge_lt_dec x y =
  sumbool_rec (\_ -> Left) (\_ -> Right) (z_ge_dec x y)

z_lt_ge_bool :: Z -> Z -> Bool
z_lt_ge_bool x y =
  bool_of_sumbool (z_lt_ge_dec x y)

all_pairs :: (List a1) -> List (Prod a1 a1)
all_pairs l =
  case l of {
   Nil -> Nil;
   Cons c cs -> Cons (Pair c c)
    (app (all_pairs cs)
      (app (map (\x -> Pair c x) cs) (map (\x -> Pair x c) cs)))}

maxlist :: (List Z) -> Z
maxlist l =
  case l of {
   Nil -> Z0;
   Cons h t ->
    case t of {
     Nil -> h;
     Cons _ _ -> max h (maxlist t)}}

max_of_nonempty_list_type :: (List a1) -> (a1 -> a1 -> Sumbool) -> Z -> (a1
                             -> Z) -> SigT a1 ()
max_of_nonempty_list_type l h1 s f =
  let {
   f0 l0 h2 s0 f1 =
     case l0 of {
      Nil -> Prelude.error "absurd case";
      Cons h t ->
       case t of {
        Nil -> (\_ -> ExistT h __);
        Cons h3 t1 ->
         let {hmax = z_ge_lt_dec (f1 h) (maxlist (map f1 (Cons h3 t1)))} in
         (\_ ->
         case hmax of {
          Left -> ExistT h __;
          Right ->
           let {f2 = f0 t h2 s0 f1 __} in
           case f2 of {
            ExistT x _ -> eq_rect t (ExistT x __) (Cons h3 t1)}})}}}
  in f0 l h1 s f __

transitive_dec_first :: (a1 -> a1 -> Sumbool) -> (a1 -> a1 -> Sumbool) -> a1
                        -> a1 -> a1 -> Sumbool
transitive_dec_first _ hp x y z =
  let {s = hp x y} in
  case s of {
   Left ->
    let {s0 = hp y z} in
    case s0 of {
     Left -> hp x z;
     Right -> Left};
   Right -> Left}

transitive_dec_second :: (a1 -> a1 -> Sumbool) -> (a1 -> a1 -> Sumbool) -> a1
                         -> a1 -> (List a1) -> Sumbool
transitive_dec_second hcd hp x y l =
  list_rec Left (\a _ iHl ->
    case iHl of {
     Left -> transitive_dec_first hcd hp x y a;
     Right -> Right}) l

transitive_dec_third :: (a1 -> a1 -> Sumbool) -> (a1 -> a1 -> Sumbool) -> a1
                        -> (List a1) -> (List a1) -> Sumbool
transitive_dec_third hcd hp x l1 l2 =
  list_rec Left (\a _ iHl1 ->
    case iHl1 of {
     Left -> transitive_dec_second hcd hp x a l2;
     Right -> Right}) l1

transitive_dec_fourth :: (a1 -> a1 -> Sumbool) -> (a1 -> a1 -> Sumbool) ->
                         (List a1) -> (List a1) -> (List a1) -> Sumbool
transitive_dec_fourth hcd hp l1 l2 l3 =
  list_rec Left (\a _ iHl1 ->
    case iHl1 of {
     Left -> transitive_dec_third hcd hp a l2 l3;
     Right -> Right}) l1

transitive_dec :: (a1 -> a1 -> Sumbool) -> (a1 -> a1 -> Sumbool) -> (List 
                  a1) -> Sumbool
transitive_dec hcd hp l =
  transitive_dec_fourth hcd hp l l l

type Finite a = SigT (List a) ()

phi_one_helper :: (a1 -> a1 -> Sumbool) -> a1 -> a1 -> Sumbool
phi_one_helper pdec x a =
  let {s = pdec x a} in
  case s of {
   Left ->
    let {s0 = pdec a x} in
    case s0 of {
     Left -> Right;
     Right -> Left};
   Right -> pdec a x}

phi_two_helper :: (a1 -> a1 -> Sumbool) -> a1 -> a1 -> a1 -> Sum () ()
phi_two_helper pdec a x a0' =
  let {s = pdec a x} in
  case s of {
   Left ->
    let {s0 = pdec a0' x} in
    case s0 of {
     Left ->
      let {s1 = pdec x a} in
      case s1 of {
       Left ->
        let {s2 = pdec x a0'} in
        case s2 of {
         Left -> Inl __;
         Right -> Inr __};
       Right ->
        let {s2 = pdec x a0'} in
        case s2 of {
         Left -> Inr __;
         Right -> Inl __}};
     Right -> Inr __};
   Right ->
    let {s0 = pdec a0' x} in
    case s0 of {
     Left -> Inr __;
     Right ->
      let {s1 = pdec x a} in
      case s1 of {
       Left ->
        let {s2 = pdec x a0'} in
        case s2 of {
         Left -> Inl __;
         Right -> Inr __};
       Right ->
        let {s2 = pdec x a0'} in
        case s2 of {
         Left -> Inr __;
         Right -> Inl __}}}}

phi_two_inhanced :: (a1 -> a1 -> Sumbool) -> a1 -> (List a1) -> a1 -> Sum 
                    () ()
phi_two_inhanced pdec a l a0' =
  list_rec (Inl __) (\a0 _ iHl ->
    case iHl of {
     Inl _ ->
      let {s = phi_two_helper pdec a a0 a0'} in
      case s of {
       Inl _ -> Inl __;
       Inr _ -> Inr __};
     Inr _ -> Inr __}) l

phi_one_dec :: (a1 -> a1 -> Sumbool) -> a1 -> (List a1) -> Sumbool
phi_one_dec pdec a l =
  list_rec Left (\a0 _ iHl ->
    case iHl of {
     Left -> phi_one_helper pdec a0 a;
     Right -> Right}) l

phi_two_dec :: (a1 -> a1 -> Sumbool) -> a1 -> (List a1) -> (List a1) ->
               Sumbool
phi_two_dec pdec a l1 l2 =
  list_rec Right (\a0 _ iHl1 ->
    case iHl1 of {
     Left -> Left;
     Right ->
      let {s = phi_two_inhanced pdec a l2 a0} in
      case s of {
       Inl _ -> Left;
       Inr _ -> Right}}) l1

phi_decidable :: (a1 -> a1 -> Sumbool) -> a1 -> (List a1) -> Sumbool
phi_decidable pdec a l =
  let {s = phi_two_dec pdec a l l} in
  case s of {
   Left -> Left;
   Right -> phi_one_dec pdec a l}

vl_or_notvl :: (a1 -> a1 -> Sumbool) -> (a1 -> a1 -> Sumbool) -> (List 
               a1) -> Sum () ()
vl_or_notvl adec pdec l =
  list_rec (Inl __) (\a l0 iHl ->
    case iHl of {
     Inl _ ->
      let {h0 = pdec a a} in
      case h0 of {
       Left -> Inr __;
       Right ->
        let {h1 = transitive_dec adec pdec (Cons a l0)} in
        case h1 of {
         Left ->
          let {h2 = phi_decidable pdec a l0} in
          case h2 of {
           Left -> Inl __;
           Right -> Inr __};
         Right -> Inr __}};
     Inr _ -> Inr __}) l

decidable_valid :: (a1 -> a1 -> Sumbool) -> (a1 -> a1 -> Sumbool) -> (Finite
                   a1) -> Sumbool
decidable_valid adec pdec h =
  case h of {
   ExistT l _ ->
    let {h0 = vl_or_notvl adec pdec l} in
    case h0 of {
     Inl _ -> Left;
     Inr _ -> Right}}

data PathT cand =
   UnitT cand cand
 | ConsT cand cand cand (PathT cand)

type Wins_type cand =
  cand -> SigT Z (Prod (PathT cand) (SigT ((Prod cand cand) -> Bool) ()))

type Loses_type cand =
  SigT Z (SigT cand (Prod (PathT cand) (SigT ((Prod cand cand) -> Bool) ())))

listify :: (List a1) -> (a1 -> a1 -> Z) -> List (Prod (Prod a1 a1) Z)
listify cand_all0 m0 =
  map (\s -> Pair (Pair (fst s) (snd s)) (m0 (fst s) (snd s)))
    (all_pairs cand_all0)

linear_search :: (a1 -> a1 -> Sumbool) -> (a1 -> a1 -> Z) -> a1 -> a1 ->
                 (List (Prod (Prod a1 a1) Z)) -> Z
linear_search dec_cand marg c d l =
  case l of {
   Nil -> marg c d;
   Cons y t ->
    case y of {
     Pair y0 k ->
      case y0 of {
       Pair c1 c2 ->
        case dec_cand c c1 of {
         Left ->
          case dec_cand d c2 of {
           Left -> k;
           Right -> linear_search dec_cand marg c d t};
         Right -> linear_search dec_cand marg c d t}}}}

mM :: (List a1) -> (a1 -> a1 -> Sumbool) -> (a1 -> a1 -> Z) -> Nat -> List
      (Prod (Prod a1 a1) Z)
mM cand_all0 dec_cand marg n =
  case n of {
   O -> listify cand_all0 marg;
   S n' ->
    let {uu = mM cand_all0 dec_cand marg n'} in
    listify cand_all0 (\c d ->
      let {u = linear_search dec_cand marg c d uu} in
      let {
       t = maxlist
             (map (\x -> min (marg c x) (linear_search dec_cand marg x d uu))
               cand_all0)}
      in
      max u t)}

m :: (List a1) -> (a1 -> a1 -> Sumbool) -> (a1 -> a1 -> Z) -> Nat -> a1 -> a1
     -> Z
m cand_all0 dec_cand marg n =
  let {l = mM cand_all0 dec_cand marg n} in
  (\c d -> linear_search dec_cand marg c d l)

iterated_marg_patht :: (List a1) -> (a1 -> a1 -> Sumbool) -> (a1 -> a1 -> Z)
                       -> Nat -> Z -> a1 -> a1 -> PathT a1
iterated_marg_patht cand_all0 dec_cand marg n s c d =
  nat_rect (\_ c0 d0 _ -> UnitT c0 d0) (\n0 iHn s0 c0 d0 _ ->
    let {
     c1 = compare0
            (linear_search dec_cand marg c0 d0
              (mM cand_all0 dec_cand marg n0))
            (maxlist
              (map (\x ->
                min (marg c0 x)
                  (linear_search dec_cand marg x d0
                    (mM cand_all0 dec_cand marg n0))) cand_all0))}
    in
    case c1 of {
     Lt ->
      let {
       h = max_of_nonempty_list_type cand_all0 dec_cand s0 (\x ->
             min (marg c0 x)
               (linear_search dec_cand marg x d0
                 (mM cand_all0 dec_cand marg n0)))}
      in
      case h of {
       ExistT x _ -> let {iHn0 = iHn s0 x d0 __} in ConsT c0 x d0 iHn0};
     _ -> iHn s0 c0 d0 __}) n s c d __

c_wins :: (List a1) -> (a1 -> a1 -> Sumbool) -> (a1 -> a1 -> Z) -> a1 -> Bool
c_wins cand_all0 dec_cand marg c =
  forallb (\d ->
    leb (m cand_all0 dec_cand marg (length cand_all0) d c)
      (m cand_all0 dec_cand marg (length cand_all0) c d)) cand_all0

iterated_marg_wins_type :: (List a1) -> (a1 -> a1 -> Sumbool) -> (a1 -> a1 ->
                           Z) -> a1 -> Wins_type a1
iterated_marg_wins_type cand_all0 dec_cand marg c d =
  let {s = m cand_all0 dec_cand marg (length cand_all0) c d} in
  ExistT s
  (let {
    hi = iterated_marg_patht cand_all0 dec_cand marg (length cand_all0) s c d}
   in
   Pair hi
   (let {r = m cand_all0 dec_cand marg (length cand_all0) d c} in
    ExistT (\x ->
    leb (m cand_all0 dec_cand marg (length cand_all0) (fst x) (snd x)) r) __))

exists_fin_reify :: (a1 -> Sumbool) -> (List a1) -> SigT a1 ()
exists_fin_reify pdec l =
  case l of {
   Nil -> Prelude.error "absurd case";
   Cons h t ->
    case pdec h of {
     Left -> ExistT h __;
     Right -> exists_fin_reify pdec t}}

reify_opponent :: (List a1) -> (a1 -> a1 -> Sumbool) -> (a1 -> a1 -> Z) -> a1
                  -> SigT a1 ()
reify_opponent cand_all0 dec_cand marg c =
  let {
   hdec = \d ->
    let {
     s = z_lt_ge_bool (m cand_all0 dec_cand marg (length cand_all0) c d)
           (m cand_all0 dec_cand marg (length cand_all0) d c)}
    in
    case s of {
     True -> Left;
     False -> Right}}
  in
  exists_fin_reify hdec cand_all0

iterated_marg_loses_type :: (List a1) -> (a1 -> a1 -> Sumbool) -> (a1 -> a1
                            -> Z) -> a1 -> Loses_type a1
iterated_marg_loses_type cand_all0 dec_cand marg c =
  let {hE = reify_opponent cand_all0 dec_cand marg c} in
  case hE of {
   ExistT d _ ->
    let {s = m cand_all0 dec_cand marg (length cand_all0) d c} in
    ExistT s (ExistT d (Pair
    (iterated_marg_patht cand_all0 dec_cand marg (length cand_all0) s d c)
    (ExistT (\x ->
    ltb (m cand_all0 dec_cand marg (length cand_all0) (fst x) (snd x)) s)
    __)))}

wins_loses_type_dec :: (List a1) -> (a1 -> a1 -> Sumbool) -> (a1 -> a1 -> Z)
                       -> a1 -> Sum (Wins_type a1) (Loses_type a1)
wins_loses_type_dec cand_all0 dec_cand marg c =
  let {b = c_wins cand_all0 dec_cand marg c} in
  case b of {
   True -> Inl (iterated_marg_wins_type cand_all0 dec_cand marg c);
   False -> Inr (iterated_marg_loses_type cand_all0 dec_cand marg c)}

type Plaintext = Z

type Ciphertext = Prod Z Z

type Ballot cand = cand -> cand -> Plaintext

type Eballot cand = cand -> cand -> Ciphertext

data HCount cand =
   Ax (List (Eballot cand)) (cand -> cand -> Ciphertext) Z
 | Cvalid (Eballot cand) (Eballot cand) (cand -> cand -> Z) Z Z (List
                                                                (Eballot
                                                                cand)) 
 (cand -> cand -> Ciphertext) (cand -> cand -> Ciphertext) (List
                                                           (Eballot cand)) 
 (HCount cand)
 | Cinvalid (Eballot cand) (Eballot cand) (cand -> cand -> Z) Z Z (List
                                                                  (Eballot
                                                                  cand)) 
 (cand -> cand -> Ciphertext) (List (Eballot cand)) (HCount cand)
 | Cdecrypt (List (Eballot cand)) (cand -> cand -> Ciphertext) (cand -> cand
                                                               -> Plaintext) 
 Z (HCount cand)
 | Fin (cand -> cand -> Z) (cand -> Bool) (cand -> Sum (Wins_type cand)
                                          (Loses_type cand)) (HCount cand)

ballot_valid_dec :: (List a1) -> (a1 -> a1 -> Sumbool) -> (Ballot a1) ->
                    Sumbool
ballot_valid_dec cand_all0 dec_cand b =
  let {x = decidable_valid dec_cand} in
  let {ht = \c d -> eq_dec0 (b c d) (Zpos XH)} in x ht (ExistT cand_all0 __)

partial_count_all_counted :: (List a1) -> (a1 -> a1 -> Sumbool) -> (a2 ->
                             (Eballot a1) -> Ballot a1) -> ((Eballot 
                             a1) -> Prod (Eballot a1) Z) -> ((a1 -> a1 ->
                             Ciphertext) -> (Eballot a1) -> a1 -> a1 ->
                             Ciphertext) -> a2 -> (List (Eballot a1)) ->
                             (List (Eballot a1)) -> (List (Eballot a1)) ->
                             (a1 -> a1 -> Ciphertext) -> (HCount a1) -> SigT
                             (List (Eballot a1))
                             (SigT (a1 -> a1 -> Ciphertext) (HCount a1))
partial_count_all_counted cand_all0 dec_cand dec0 permute add_eballots kpriv bs0 ts inbs m0 hc =
  case ts of {
   Nil -> ExistT inbs (ExistT m0 hc);
   Cons u us ->
    let {p = permute u} in
    case p of {
     Pair v zkppermuv ->
      let {b = dec0 kpriv v} in
      let {s = ballot_valid_dec cand_all0 dec_cand b} in
      case s of {
       Left ->
        let {w = add_eballots m0 u} in
        partial_count_all_counted cand_all0 dec_cand dec0 permute
          add_eballots kpriv bs0 us inbs w (Cvalid u v b zkppermuv Z0 us m0 w
          inbs hc);
       Right ->
        partial_count_all_counted cand_all0 dec_cand dec0 permute
          add_eballots kpriv bs0 us (Cons u inbs) m0 (Cinvalid u v b
          zkppermuv Z0 us m0 inbs hc)}}}

all_ballots_counted :: (List a1) -> (a1 -> a1 -> Sumbool) -> (a2 -> (Ballot
                       a1) -> Eballot a1) -> (a3 -> (Eballot a1) -> Ballot
                       a1) -> ((Eballot a1) -> Prod (Eballot a1) Z) -> ((a1
                       -> a1 -> Ciphertext) -> (Eballot a1) -> a1 -> a1 ->
                       Ciphertext) -> a3 -> a2 -> (List (Eballot a1)) -> SigT
                       (List (Eballot a1))
                       (SigT (a1 -> a1 -> Ciphertext) (HCount a1))
all_ballots_counted cand_all0 dec_cand enc0 dec0 permute add_eballots kpriv kpub bs0 =
  let {
   x = partial_count_all_counted cand_all0 dec_cand dec0 permute add_eballots
         kpriv bs0 bs0 Nil (enc0 kpub (\_ _ -> Z0))}
  in
  let {h = Ax bs0 (enc0 kpub (\_ _ -> Z0)) Z0} in x h

decrypt_margin :: (List a1) -> (a1 -> a1 -> Sumbool) -> (a2 -> (Ballot 
                  a1) -> Eballot a1) -> (a3 -> (Eballot a1) -> Ballot 
                  a1) -> ((Eballot a1) -> Prod (Eballot a1) Z) -> ((a1 -> a1
                  -> Ciphertext) -> (Eballot a1) -> a1 -> a1 -> Ciphertext)
                  -> a3 -> a2 -> (List (Eballot a1)) -> SigT
                  (a1 -> a1 -> Plaintext) (HCount a1)
decrypt_margin cand_all0 dec_cand enc0 dec0 permute add_eballots kpriv kpub bs0 =
  let {
   s = all_ballots_counted cand_all0 dec_cand enc0 dec0 permute add_eballots
         kpriv kpub bs0}
  in
  case s of {
   ExistT i s0 ->
    case s0 of {
     ExistT encm p ->
      let {x = \x -> Cdecrypt i encm (dec0 kpriv encm) Z0 x} in
      let {x0 = x p} in ExistT (dec0 kpriv encm) x0}}

schulze_winners :: (List a1) -> (a1 -> a1 -> Sumbool) -> (a2 -> (Ballot 
                   a1) -> Eballot a1) -> (a3 -> (Eballot a1) -> Ballot 
                   a1) -> ((Eballot a1) -> Prod (Eballot a1) Z) -> ((a1 -> a1
                   -> Ciphertext) -> (Eballot a1) -> a1 -> a1 -> Ciphertext)
                   -> a3 -> a2 -> (List (Eballot a1)) -> SigT (a1 -> Bool)
                   (HCount a1)
schulze_winners cand_all0 dec_cand enc0 dec0 permute add_eballots kpriv kpub bs0 =
  let {
   s = decrypt_margin cand_all0 dec_cand enc0 dec0 permute add_eballots kpriv
         kpub bs0}
  in
  case s of {
   ExistT dm h -> ExistT (c_wins cand_all0 dec_cand dm) (Fin dm
    (c_wins cand_all0 dec_cand dm)
    (wins_loses_type_dec cand_all0 dec_cand dm) h)}

data Cand =
   A
 | B

cand_rect :: a1 -> a1 -> Cand -> a1
cand_rect f f0 c =
  case c of {
   A -> f;
   B -> f0}

cand_rec :: a1 -> a1 -> Cand -> a1
cand_rec =
  cand_rect

cand_all :: List Cand
cand_all =
  Cons A (Cons B Nil)

cand_eq_dec :: Cand -> Cand -> Sumbool
cand_eq_dec a b =
  cand_rec (cand_rec Left Right b) (cand_rec Right Left b) a

type KPub =
  Z
  -- singleton inductive, whose constructor was pubkey
  
type KPriv =
  Z
  -- singleton inductive, whose constructor was prikey
  
b1 :: Ballot Cand
b1 c d =
  case c of {
   A ->
    case d of {
     A -> Z0;
     B -> Zpos XH};
   B -> Z0}

e1 :: Eballot Cand
e1 c d =
  case c of {
   A ->
    case d of {
     A -> Pair Z0 Z0;
     B -> Pair (Zpos XH) Z0};
   B -> Pair Z0 Z0}

enc :: KPub -> (Ballot Cand) -> Eballot Cand
enc _ _ =
  e1

dec :: KPriv -> (Eballot Cand) -> Ballot Cand
dec _ _ =
  b1

dummy_fun :: (Eballot Cand) -> Prod (Eballot Cand) Z
dummy_fun e =
  Pair e Z0

add_enc_marging :: (Cand -> Cand -> Ciphertext) -> (Eballot Cand) -> Cand ->
                   Cand -> Prod Z Z
add_enc_marging m0 e c d =
  case m0 c d of {
   Pair f _ ->
    case e c d of {
     Pair s _ -> Pair (add0 f s) Z0}}

schulze_all :: (List (Eballot Cand)) -> SigT (Cand -> Bool) (HCount Cand)
schulze_all =
  schulze_winners cand_all cand_eq_dec enc dec dummy_fun add_enc_marging Z0
    Z0

bs :: List (Eballot Cand)
bs =
  Cons e1 (Cons e1 (Cons e1 (Cons e1 (Cons e1 Nil))))

schulze_win :: SigT (Cand -> Bool) (HCount Cand)
schulze_win =
  schulze_all bs

schulze_winners_pf :: SigT (Cand -> Bool) (HCount Cand)
schulze_winners_pf =
  schulze_win


printfn = 
   case schulze_winners_pf of
     ExistT f a -> [f A, f B]     
