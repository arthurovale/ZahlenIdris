module Integer

%default total

||| Integer type.
||| Reasoning is that first Nat is the number of successor applications and
||| Second Nat is number of predecessor applications.
data Zahlen = I Nat Nat

--------------------------------------------------------------------------------
-----------------------------  Cannonicalizer  ---------------------------------
--------------------------------------------------------------------------------
||| reduce reduces an inhabitant of Z to 0-form (i.e. if (I a b) is such an
||| inhabitant then it reduces (I a b) to (I 0 b') or (I a' 0)).
reduce : Zahlen -> Zahlen
reduce (I s p) = reduce' s p where
  reduce' (S s) (S p) = reduce' s p
  reduce' s p = I s p

--------------------------------------------------------------------------------
-------------------------  Successor/Predecessor  ------------------------------
--------------------------------------------------------------------------------
-- These are defined to give the impression of the natural representations of --
--        integers as an extension of peano arithmetic by P and S             --
--------------------------------------------------------------------------------
namespace ZahlenSPZ
  Z : Zahlen
  Z = (I 0 0)

  S : Zahlen -> Zahlen
  S (I s p) = I (s + 1) p

  P : Zahlen -> Zahlen
  P (I s p) = I s (p + 1)

--------------------------------------------------------------------------------
---------------------------  Integer Interfaces  -------------------------------
--------------------------------------------------------------------------------
||| Cast implementation from Zahlen to Integer.
Cast Zahlen Integer where
  cast (I s p) = (fromNat s) - (fromNat p)

||| Cast implementation from Integer to Zahlen.
Cast Integer Zahlen where
  cast int = case compare int 0 of
                  LT => I 0 (fromInteger (negate int))
                  EQ => I 0 0
                  GT => I (fromInteger int) 0

||| Show implementation interface.
Show Zahlen where
  show = show . the Integer . cast

||| Implementation of Eq for Zahlen.
Eq Zahlen where
  (==) (I s1 p1) (I s2 p2) = (s1 + p2 == s2 + p1)

||| Implementation of Ord for Zahlen.
Ord Zahlen where
  compare (I s1 p1) (I s2 p2) = compare (s1 + p2) (s2 + p1)

||| Implementation of Num for Zahlen.
Num Zahlen where
  (+) (I s1 p1) (I s2 p2) = I (s1 + s2) (p1 + p2)
  (*) (I s1 p1) (I s2 p2) = I (s1 * s2 + p1 * p2) (s1 * p2 + p1 * s2)
  fromInteger = cast

||| Implemenation of Neg for Zahlen.
Neg Zahlen where
  negate (I s p) = I p s
  (-) x y = (+) x (negate y)
  abs x = if (x > 0) then x else negate x

--------------------------------------------------------------------------------
---------------------------------  Tests  --------------------------------------
--------------------------------------------------------------------------------
--    These are analogous to the "Syntatical Tests" section of Prelude.Nat    --
--      But syntatical analysis is harder, and therefore we rely on ==        --
--------------------------------------------------------------------------------
||| Checks if Integer is 0.
isZero : Zahlen -> Bool
isZero = (0 ==)
||| Checks if Integer would have normal form of only successor function app.
isSucc : Zahlen -> Bool
isSucc = (> 0)
||| Checks if Integer would have normal form of only predecessor function app.
isPred : Zahlen -> Bool
isPred = (< 0)

--------------------------------------------------------------------------------
-------------------------------  Nat Lemmas  -----------------------------------
--------------------------------------------------------------------------------
namespace NatTrans
  infixr 0 =>>
  ||| Infix notation for Nat trans to soft on chaining proof applications.
  ||| Chaining goes to the right. Used to change the right
  ||| hand side of equality.
  (=>>) : (a = b) -> (b = c) -> (a = c)
  (=>>) = trans
  infixr 0 <<=
  ||| Infix notation for Nat trans to soft on chaining proof applications.
  ||| Chaining goes to the left but equalities are declared as if to the right.
  ||| Used to change the left hand side of equality.
  (<<=) : (b = c) -> (b = a) -> (c = a)
  (<<=) prf1 prf2 = trans (sym prf1) prf2
namespace plusLeftRightNat
  ||| Adding on left and right doesn't change result.
  plusLeftRight : {l1, l2, r1, r2 : Nat} ->
                  l1 = l2 -> r1 = r2 -> l1 + r1 = l2 + r2
  plusLeftRight {l1} {l2} {r1} {r2} prf1 prf2 =
    rewrite prf2 in (plusConstantRight l1 l2 r2 prf1)

||| Bicommutativity of Natural Numbers addition.
||| Used to prove commutativity of Integer addition.
biCommutativity : {s1, p1, s2, p2 : Nat} ->
                  (s1 + s2) + (p2 + p1) = (s2 + s1) + (p1 + p2)
biCommutativity {s1} {p1} {s2} {p2} = rewrite plusCommutative p1 p2 in
  plusConstantRight (s1 + s2) (s2 + s1) (p2 + p1) (plusCommutative s1 s2)

namespace NatmultConstantRight
  ||| (=) is invariant upon multiplying constants to the right.
  ||| @ l natural to the left of equality
  ||| @ r natural to the right of equality
  ||| @ c constant to be added
  ||| @ prf proof that l = r
  multConstantRight : (l : Nat) -> (r : Nat) -> (c : Nat) ->
                      (prf : l = r) -> l * c = r * c
  multConstantRight l r c prf = rewrite prf in Refl

  ||| (=) is invariant upon multiplying constants to the left.
  ||| @ l natural to the left of equality
  ||| @ r natural to the right of equality
  ||| @ c constant to be added
  ||| @ prf proof that l = r
  multConstantLeft : (l : Nat) -> (r : Nat) -> (c : Nat) ->
                     (prf : l = r) -> c * l = c * r
  multConstantLeft l r c prf = rewrite prf in Refl

ltePlusConstantRight : {l, l' : Nat} -> LTE l l' -> (c : Nat) ->
                       LTE (l + c) (l' + c)
ltePlusConstantRight LTEZero Z = LTEZero
ltePlusConstantRight (LTESucc {left = l} {right = r} x) Z =
                            rewrite (plusZeroRightNeutral r) in
                              (rewrite (plusZeroRightNeutral l) in (LTESucc x))
ltePlusConstantRight {l} {l'} prf (S c) = rewrite sym rew1 in
                                      (rewrite sym rew2 in
                                        (ltePlusConstantRight (LTESucc prf) c))
  where
    rew1 : plus (S l') c = plus l' (S c)
    rew1 = plusCommutative (S l') c =>>
           sym (plusSuccRightSucc c l') =>>
           cong (plusCommutative c l') =>>
           plusSuccRightSucc l' c
    rew2 : plus (S l) c = plus l (S c)
    rew2 = plusCommutative (S l) c =>>
           sym (plusSuccRightSucc c l) =>>
           cong (plusCommutative c l) =>>
           plusSuccRightSucc l c

ltePlusConstantLeft : {r, r' : Nat} -> LTE r r' -> (c : Nat) ->
                      LTE (c + r) (c + r')
ltePlusConstantLeft {r} {r'} prf c = rewrite plusCommutative c r' in
                                      (rewrite plusCommutative c r in
                                        ltePlusConstantRight prf c)

ltePlus : {l, l', r, r' : Nat} -> LTE l l' -> LTE r r' -> LTE (l + r) (l' + r')
ltePlus {l} {l'} {r} {r'} lte1 lte2 =
  lteTransitive (ltePlusConstantRight lte1 r) (ltePlusConstantLeft lte2 l')

ltePlusLeftCancel : (r : Nat) -> (r' : Nat) -> (c : Nat) ->
                    LTE (c + r) (c + r') -> LTE r r'
ltePlusLeftCancel _ _  Z prf = prf
ltePlusLeftCancel _ _  (S c) LTEZero impossible
ltePlusLeftCancel r r' (S c) (LTESucc prf) = ltePlusLeftCancel r r' c prf

ltePlusRightCancel : (l : Nat) -> (l' : Nat) -> (c : Nat) ->
                    LTE (l + c) (l' + c) -> LTE l l'
ltePlusRightCancel l l' c prf =
  ltePlusLeftCancel l l' c
    (rewrite plusCommutative c l' in (rewrite plusCommutative c l in prf))

--------------------------------------------------------------------------------
--------------------------------- Comparisons ----------------------------------
--------------------------------------------------------------------------------

||| Proofs that `n` or `m` is not equal to Z
data NotBothZero : (n, m : Zahlen) -> Type where
  LeftIsNotZero  : {sn, pn, sm, pm : Nat} -> {auto prf : Not (sn = pn)} ->
                   NotBothZero (I sn pn) (I sm pm)
  RightIsNotZero : {sn, pn, sm, pm : Nat} -> {auto prf : Not (sm = pm)} ->
                   NotBothZero (I sn pn) (I sm pm)

||| Proofs that `n` is less than or equal to `m`
||| @ n the smaller number
||| @ m the larger number
data LTE  : (n, m : Zahlen) -> Type where
  ZLTE : {s1, p1, s2, p2 : Nat} -> {auto prf : LTE (s1 + p2) (s2 + p1)} ->
         LTE (I s1 p1) (I s2 p2)

||| Greater than or equal to
GTE : Zahlen -> Zahlen -> Type
GTE l r = LTE r l

||| Strict less than
LT : Zahlen -> Zahlen -> Type
LT l r = LTE (S l) r

||| Strict greater than
GT : Zahlen -> Zahlen -> Type
GT l r = LT r l

||| A decision procedure for `LTE`
isLTE : (m, n : Zahlen) -> Dec (m `LTE` n)
isLTE (I sm pm) (I sn pn) = case isLTE (sm + pn) (sn + pm) of
                                 (Yes prf) => Yes ZLTE
                                 (No contra) => No (lemma contra)
    where
      lemma : (LTE (sm + pn) (sn + pm) -> Void) ->
              (LTE (I sm pm) (I sn pn) -> Void)
      lemma contra (ZLTE {prf = prf})  = contra prf

||| LTE is reflexive.
lteRefl : {z : Zahlen} -> LTE z z
lteRefl {z = I s p} = ZLTE {prf = lteRefl}

||| `LTE` is transitive
lteTransitive : {n, m, p : Zahlen} -> LTE n m -> LTE m p -> LTE n p
lteTransitive {n = I sn pn} {m = I sm pm} {p = I sp pp} (ZLTE {prf = prf1})
              (ZLTE {prf = prf2}) =
  ZLTE {prf = lemma prf1 prf2}
  where
    rew1 : ((sn + pm) + (sm + pp)) = (sn + pp) + (sm + pm)
    rew1 = sym (plusAssociative sn pm (sm + pp)) =>>
          plusConstantLeft (pm + (sm + pp)) (pp + (sm + pm)) sn
            (plusAssociative pm sm pp =>>
            plusCommutative (pm + sm) pp =>>
            plusConstantLeft (pm + sm) (sm + pm) pp (plusCommutative pm sm)) =>>
          plusAssociative sn pp (sm + pm)

    rew2 : ((sm + pn) + (sp + pm)) = ((sp + pn) + (sm + pm))
    rew2 = plusLeftRight (plusCommutative sm pn) (plusCommutative sp pm) =>>
          sym (plusAssociative pn sm (pm + sp)) =>>
          plusConstantLeft (sm + (pm + sp)) (sp + (sm + pm)) pn
            (plusAssociative sm pm sp =>>
            plusCommutative (sm + pm) sp) =>>
          (plusAssociative pn sp (sm + pm)) =>>
          plusConstantRight (pn + sp) (sp + pn) (sm + pm)
            (plusCommutative pn sp)

    lemma : LTE (sn + pm) (sm + pn) -> LTE (sm + pp) (sp + pm) ->
            LTE (sn + pp) (sp + pn)
    lemma prf1 prf2 = ltePlusRightCancel (sn + pp) (sp + pn) (sm + pm)
                  (rewrite sym rew2 in (rewrite sym rew1 in ltePlus prf1 prf2))

||| Boolean test than one Zahlen is less than or equal to another
lte : Zahlen -> Zahlen -> Bool
lte (I sl pl) (I sr pr) = lte (sl + pr) (sr + pl)

||| Boolean test than one Zahlen is greater than or equal to another
gte : Zahlen -> Zahlen -> Bool
gte l r = lte r l

||| Boolean test that one Zhalen is equal to another
eq : Zahlen -> Zahlen -> Bool
eq l r = lte l r && gte l r

||| Boolean test than one Zahlen is strictly less than another
lt : Zahlen -> Zahlen -> Bool
lt l r = lte (S l) r

||| Boolean test than one Zahlen is strictly greater than another
gt : Zahlen -> Zahlen -> Bool
gt l r = lt r l

--------------------------------------------------------------------------------
--------------  Equivalence Relation for Nat-Pair Representation  --------------
--------------------------------------------------------------------------------
||| Equivalence relation type between different integers.
data Equiv : Zahlen -> Zahlen -> Type where
  ZRefl : {auto prf : s1 + p2 = s2 + p1} -> Equiv (I s1 p1) (I s2 p2)
infixr 0 <=>
||| Defines an infix operator for Equiv analogous to (=).
(<=>) : Zahlen -> Zahlen -> Type
(<=>) = Equiv

||| Reflexive property of equivalence relation.
refl : {z : Zahlen} -> (z <=> z)
refl {z = I s p} = ZRefl

||| Symmetric property of Equiv, extended from sym for Nats.
||| @ l left integer
||| @ r right integer
sym : {l : Zahlen} -> {r : Zahlen} -> (l <=> r) -> (r <=> l)
sym (ZRefl {prf}) = ZRefl {prf = sym prf}

||| Trans property of Equiv.
||| @ l left integer
||| @ c center integer
||| @ r right integer
trans : {l, c, r : Zahlen} -> (l <=> c) -> (c <=> r) -> (l <=> r)
trans {l = I s1 p1} {c = I s2 p2} {r = I s3 p3} (ZRefl {prf = prfl})
  (ZRefl {prf = prfr}) = ZRefl {prf = lemma prfl prfr}
  where
    lemma : s1 + p2 = s2 + p1 -> s2 + p3 = s3 + p2 -> s1 + p3 = s3 + p1
    lemma prfl prfr = plusLeftCancel (s2 + p2) (s1 + p3) (s3 + p1)
                      (plusConstantLeft (p3 + s1) (s1 + p3) (s2 + p2)
                        (plusCommutative p3 s1) <<=
                      plusAssociative s2 p2 (p3 + s1) <<=
                      plusConstantLeft ((p2 + p3) + s1) (p2 + (p3 + s1)) s2
                              (sym (plusAssociative p2 p3 s1)) <<=
                      plusConstantLeft ((p3 + p2) + s1) ((p2 + p3) + s1) s2
                              (plusConstantRight (p3 + p2) (p2 + p3) s1
                              (plusCommutative p3 p2)) <<=
                      plusConstantLeft (p3 + (p2 + s1)) ((p3 + p2) + s1) s2
                              (plusAssociative p3 p2 s1) <<=
                      plusConstantLeft (p3 + (s1 + p2)) (p3 + (p2 + s1)) s2
                          (plusConstantLeft (s1 + p2) (p2 + s1) p3
                          (plusCommutative s1 p2)) <<=
                      sym (plusAssociative s2 p3 (s1 + p2)) <<=
                      plusCommutative (s1 + p2) (s2 + p3) <<=
                      plusLeftRight prfl prfr =>>
                      sym (plusAssociative s2 p1 (s3 + p2)) =>>
                      plusConstantLeft (p1 + (s3 + p2)) (p1 + (p2 + s3)) s2
                              (plusConstantLeft (s3 + p2)
                              (p2 + s3) p1 (plusCommutative s3 p2)) =>>
                      plusConstantLeft (p1 + (p2 + s3)) ((p1 + p2) + s3) s2
                              (plusAssociative p1 p2 s3) =>>
                      plusConstantLeft ((p1 + p2) + s3) ((p2 + p1) + s3) s2
                              (plusConstantRight (p1 + p2) (p2 + p1) s3
                              (plusCommutative p1 p2)) =>>
                      plusConstantLeft ((p2 + p1) + s3) (p2 + (p1 + s3)) s2
                              (sym (plusAssociative p2 p1 s3)) =>>
                      plusAssociative s2 p2 (p1 + s3) =>>
                      plusConstantLeft (p1 + s3) (s3 + p1) (s2 + p2)
                        (plusCommutative p1 s3)
                    )

namespace ZahlenTrans
  infixr 0 =>>
  ||| Infix notation for Zahlen trans to soft on chaining proof applications.
  ||| Chaining goes to the right. Used to change the right hand side
  ||| of equality.
  (=>>) : (a <=> b) -> (b <=> c) -> (a <=> c)
  (=>>) = trans
  infixr 0 <<=
  ||| Infix notation for Zahlen trans to soft on chaining proof applications.
  ||| Chaining goes to the left but equalities are declared as if to the right.
  ||| Used to change the left hand side of equality.
  (<<=) : (b <=> c) -> (b <=> a) -> (c <=> a)
  (<<=) prf1 prf2 = trans (sym prf1) prf2

--------------------------------------------------------------------------------
----------------------  Well-Definedeness and Induction  -----------------------
--------------------------------------------------------------------------------
||| Type that captures Well-Definedeness. There is a single constructor WD
||| WD establishes well-defideness of a function under the equivalence
||| classe of Equiv.
data WellDef : (Zahlen -> Zahlen) -> Type where
    WD : (f : Zahlen -> Zahlen) ->
         ((l : Zahlen) -> (r : Zahlen) -> l <=> r -> f l <=> f r) -> WellDef f

--------------------------------------------------------------------------------
-------------------------  Integer S and P Proofs  -----------------------------
--------------------------------------------------------------------------------

||| S preserves equality
eqSucc : (l : Zahlen) -> (r : Zahlen) ->  (prf : l <=> r) -> S l <=> S r
eqSucc (I sl pl) (I sr pr) (ZRefl {prf}) = ZRefl {prf = lemma prf}
  where
    lemma : sl + pr = sr + pl -> (sl + 1) + pr = (sr + 1) + pl
    lemma prf = plusAssociative sl 1 pr <<=
          plusConstantLeft (pr + 1) (1 + pr) sl (plusCommutative pr 1) <<=
          sym (plusAssociative sl pr 1) <<=
          plusConstantRight (sl + pr) (sr + pl) 1 prf =>>
          sym (plusAssociative sr pl 1) =>>
          plusConstantLeft (pl + 1) (1 + pl) sr (plusCommutative pl 1) =>>
          plusAssociative sr 1 pl

||| P preserves equality
eqPred : (l : Zahlen) -> (r : Zahlen) ->  (prf : l <=> r) -> P l <=> P r
eqPred (I sl pl) (I sr pr) (ZRefl {prf}) = ZRefl {prf = lemma prf}
  where
    lemma : sl + pr = sr + pl -> sl + (pr + 1) = sr + (pl +1)
    lemma prf = sym (plusAssociative sl pr 1) <<=
          plusConstantRight (sl + pr) (sr + pl) 1 prf =>>
          sym (plusAssociative sr pl 1)

succWellDef : WellDef S
succWellDef = WD S eqSucc

predWellDef : WellDef P
predWellDef = WD P eqPred

||| S is injective
succInjective : (l : Zahlen) -> (r : Zahlen) -> (prf : S l <=> S r) -> l <=> r
succInjective (I sl pl) (I sr pr) (ZRefl {prf}) = ZRefl {prf = lemma prf}
  where
    lemma : (sl + 1) + pr = (sr + 1) + pl -> sl + pr = sr + pl
    lemma prf = plusLeftCancel 1 (sl + pr) (sr + pl)
                (
                plusAssociative 1 sl pr <<=
                plusConstantRight (sl + 1) (1 + sl) pr
                  (plusCommutative sl 1) <<=
                prf =>>
                plusConstantRight (sr + 1) (1 + sr) pl
                  (plusCommutative sr 1) =>>
                plusAssociative 1 sr pl
                )

||| S is surjective
succSurjective : (y : Zahlen) -> (x : Zahlen ** S x <=> y)
succSurjective (I s p) = (I s (p + 1) ** ZRefl {prf = lemma})
  where
    lemma : (s + 1) + p = s + (p + 1)
    lemma = sym (plusAssociative s 1 p) =>>
          plusConstantLeft (1 + p) (p + 1) s (plusCommutative 1 p)

||| P is injective
predInjective : (l : Zahlen) -> (r : Zahlen) -> (prf : P l <=> P r) -> l <=> r
predInjective (I sl pl) (I sr pr) (ZRefl {prf}) = ZRefl {prf = lemma prf}
  where
    lemma : sl + (pr + 1) = sr + (pl + 1) -> sl + pr = sr + pl
    lemma prf = plusRightCancel (sl + pr) (sr + pl) 1
                (
                plusAssociative sl pr 1 <<=
                prf =>>
                plusAssociative sr pl 1
                )

||| S is surjective
predSurjective : (y : Zahlen) -> (x : Zahlen ** P x <=> y)
predSurjective (I s p) = (I (s + 1) p ** ZRefl {prf = lemma})
  where
    lemma : (s + 1) + p = s + (p + 1)
    lemma = sym (plusAssociative s 1 p) =>>
          plusConstantLeft (1 + p) (p + 1) s (plusCommutative 1 p)

SPCommute : (z : Zahlen) -> S (P z) <=> P (S z)
SPCommute (I s p) = ZRefl

SPCancel : (z : Zahlen) -> S (P z) <=> z
SPCancel (I s p) = ZRefl {prf = lemma}
  where
    lemma : (s + 1) + p = s + (p + 1)
    lemma = sym (plusAssociative s 1 p) =>>
            plusConstantLeft (1 + p) (p + 1) s (plusCommutative 1 p)

PSCancel : (z : Zahlen) -> P (S z) <=> z
PSCancel z = sym (SPCommute z) =>> SPCancel z

--------------------------------------------------------------------------------
------------------------  Integer Addition Proofs  -----------------------------
--------------------------------------------------------------------------------
||| Proof of commutativity of addition using biCommutativity Lemma.
||| @ l left integer
||| @ r right integer
plusCommutative : (l : Zahlen) -> (r : Zahlen) -> l + r <=> r + l
plusCommutative (I s1 p1) (I s2 p2) = ZRefl {prf = biCommutativity}

||| Successor distributes through addition to the right term.
||| @ l left integer
||| @ r right integer
plusSuccRightSucc : (l : Zahlen) -> (r : Zahlen) -> S (l + r) <=> l + (S r)
plusSuccRightSucc (I sl pl) (I sr pr) = ZRefl {prf = lemma}
  where
    lemma : ((sl + sr) + 1) + (pl + pr) = (sl + (sr + 1)) + (pl + pr)
    lemma = plusConstantRight ((sl + sr) + 1) (sl + (sr + 1)) (pl + pr)
              (sym (plusAssociative sl sr 1))

||| Successor distributes through addition to the left term.
||| @ l left integer
||| @ r right integer
plusSuccLeftSucc : (l : Zahlen) -> (r : Zahlen) -> S (l + r) <=> (S l) + r
plusSuccLeftSucc l r = eqSucc (l + r) (r + l) (plusCommutative l r) =>>
                       plusSuccRightSucc r l =>> plusCommutative r (S l)

||| Proof that successor is equivalent to addition by 1.
||| @ z left integer
plusOneSucc : (z : Zahlen) -> 1 + z <=> S z
plusOneSucc (I s p) = ZRefl {prf = lemma}
  where
    lemma : S (s + p) = (s + 1) + p
    lemma = Refl =>>
            plusAssociative 1 s p =>>
            plusConstantRight (1 + s) (s + 1) p (plusCommutative 1 s)

||| Predecessor distributes through addition to the right term.
||| @ l left integer
||| @ r right integer
plusPredRightPred : (l : Zahlen) -> (r : Zahlen) -> P (l + r) <=> l + (P r)
plusPredRightPred (I sl pl) (I sr pr) = ZRefl {prf = lemma}
  where
    lemma : (sl + sr) + (pl + (pr + 1)) = (sl + sr) + ((pl + pr) + 1)
    lemma = plusConstantLeft (pl + (pr + 1)) ((pl + pr) + 1) (sl + sr)
      (plusAssociative pl pr 1)

||| Predecessor distributes through addition to the right term.
||| @ l left integer
||| @ r right integer
plusPredLeftPred : (l : Zahlen) -> (r : Zahlen) -> P (l + r) <=> (P l) + r
plusPredLeftPred l r = eqPred (l + r) (r + l) (plusCommutative l r) =>>
                        plusPredRightPred r l =>> plusCommutative r (P l)

||| Predecessor invariant from addition by 1.
plusOnePred : (z : Zahlen) -> (P z) + 1 <=> z
plusOnePred (I s p) = ZRefl {prf = lemma}
  where
    lemma : (s + 1) + p = s + ((p + 1) + 0)
    lemma = sym (plusAssociative s 1 p) =>>
          plusConstantLeft (1 + p) ((p + 1) + 0) s
            (plusCommutative 1 p =>> sym (plusZeroRightNeutral (p + 1)))

||| Integer addition is associative.
||| @ l left operand
||| @ c center operand
||| @ r right operand
plusAssociative : (l : Zahlen) -> (c : Zahlen) -> (r : Zahlen) ->
                  l + (c + r) <=> (l + c) + r
plusAssociative (I sl pl) (I sc pc) (I sr pr) =
  ZRefl {prf = plusLeftRight (plusAssociative sl sc sr)
    (sym (plusAssociative pl pc pr))}

||| Zero is neutral element of addition by the left.
||| @ r integer added to zero through the right
plusZeroLeftNeutral : (r : Zahlen) -> 0 + r <=> r
plusZeroLeftNeutral (I s p) = ZRefl

||| Zero is neutral element of addition by the right.
||| @ l integer added to zero through the left
plusZeroRightNeutral : (l : Zahlen) -> l + 0 <=> l
plusZeroRightNeutral l = plusCommutative l 0 =>> plusZeroLeftNeutral l

||| Equiv is invariant upon adding constants to the right.
||| @ l integer to the left of equality
||| @ r integer to the right of equality
||| @ c constant to be added
||| @ prf proof that l <=> r
plusConstantRight : (l : Zahlen) -> (r : Zahlen) ->
                    (c : Zahlen) -> (prf : l <=> r) -> l + c <=> r + c
plusConstantRight (I sl pl) (I sr pr) (I sc pc) (ZRefl {prf})
  = ZRefl {prf = lemma prf}
  where
    lemma : (sl + pr) = (sr + pl) ->
            (sl + sc) + (pr + pc) = (sr + sc) + (pl + pc)
    lemma prf = sym (plusAssociative sl sc (pr + pc)) =>>
                plusConstantLeft (sc + (pr + pc)) ((sc + pr) + pc) sl
                  (plusAssociative sc pr pc) =>>
                plusConstantLeft ((sc + pr) + pc) ((pr + sc) + pc) sl
                  (plusConstantRight (sc + pr) (pr + sc) pc
                  (plusCommutative sc pr)) =>>
                plusConstantLeft ((pr + sc) + pc) (pr + (sc + pc)) sl
                  (sym (plusAssociative pr sc pc)) =>>
                plusAssociative sl pr (sc + pc) =>>
                rewrite prf in Refl =>>
                sym (plusAssociative sr pl (sc + pc)) =>>
                plusConstantLeft (pl + (sc + pc)) ((pl + sc) + pc) sr
                  (plusAssociative pl sc pc) =>>
                plusConstantLeft ((pl + sc) + pc) ((sc + pl) + pc) sr
                  (plusConstantRight (pl + sc) (sc + pl) pc
                  (plusCommutative pl sc)) =>>
                plusConstantLeft ((sc + pl) + pc) (sc + (pl + pc)) sr
                  (sym (plusAssociative sc pl pc)) =>>
                plusAssociative sr sc (pl + pc)

||| Equiv is invariant upon adding constants to the left,
||| follows from commutativity.
||| @ l integer to the left of equality
||| @ r integer to the right of equality
||| @ c constant to be added
||| @ prf proof that l <=> r
plusConstantLeft : (l : Zahlen) -> (r : Zahlen) ->
                   (c : Zahlen) -> (prf : l <=> r) -> c + l <=> c + r
plusConstantLeft l r c prf = plusCommutative l c <<=
                             plusConstantRight l r c prf =>>
                             plusCommutative r c

namespace plusLeftRightZahlen
  plusLeftRight : {l1, l2, r1, r2 : Zahlen} ->
                  l1 <=> l2 -> r1 <=> r2 -> l1 + r1 <=> l2 + r2
  plusLeftRight {l1} {l2} {r1} {r2} prf1 prf2 =
    plusConstantRight l1 l2 r1 prf1 =>> plusConstantLeft r1 r2 l2 prf2

||| Constants to the left of both sides of Equiv can be cancelled.
||| @ l constant to be removed
||| @ r integer to the left of equality
||| @ r' equivalent integer to the right of equality
||| @ prf proof that l + r <=> l + r'
plusLeftCancel : (l : Zahlen) -> (r : Zahlen) -> (r' : Zahlen) ->
                 (prf : l + r <=> l + r') -> r <=> r'
plusLeftCancel (I sl pl) (I sr pr) (I sr' pr') (ZRefl {prf}) =
  ZRefl {prf = lemma prf}
    where
      lemma : (sl + sr) + (pl + pr') = (sl + sr') + (pl + pr) ->
              sr + pr' = sr' + pr
      lemma prf = plusLeftCancel (sl + pl) (sr + pr') (sr' + pr)
                  (
                  plusAssociative sl pl (sr + pr') <<=
                  plusConstantLeft ((pl + sr) + pr') (pl + (sr + pr')) sl
                          (sym (plusAssociative pl sr pr')) <<=
                  plusConstantLeft ((sr + pl) + pr') ((pl + sr) + pr') sl
                          (plusConstantRight (sr + pl) (pl + sr) pr'
                          (plusCommutative sr pl)) <<=
                  plusConstantLeft (sr + (pl + pr')) ((sr + pl) + pr') sl
                          (plusAssociative sr pl pr') <<=
                  sym (plusAssociative sl sr (pl + pr')) <<=
                  prf =>>
                  sym (plusAssociative sl sr' (pl + pr)) =>>
                  plusConstantLeft (sr' + (pl + pr)) ((sr' + pl) + pr) sl
                          (plusAssociative sr' pl pr) =>>
                  plusConstantLeft ((sr' + pl) + pr) ((pl + sr') + pr) sl
                          (plusConstantRight (sr' + pl) (pl + sr') pr
                          (plusCommutative sr' pl)) =>>
                  plusConstantLeft ((pl + sr') + pr) (pl + (sr' + pr)) sl
                          (sym (plusAssociative pl sr' pr)) =>>
                  plusAssociative sl pl (sr' + pr)
                  )

||| Constants to the right of both sides of Equiv can be cancelled.
||| @ l integer to the left of equality
||| @ l' equivalent integer to the right of equality
||| @ r constant to be removed
||| @ prf proof that l + r <=> l' + r
plusRightCancel : (l : Zahlen) -> (l' : Zahlen) -> (r : Zahlen) ->
                  (prf : l + r <=> l' + r) -> l <=> l'
plusRightCancel l l' r prf = plusLeftCancel r l l'
                             (
                             plusCommutative l r <<=
                             prf =>>
                             plusCommutative l' r
                             )

||| Right cancelling of lone constant on the right yields 0.
||| @ l constant to be cancelled
||| @ r integer to be proven to be 0
||| @ prf proof hat l + r <=> l
plusLeftLeftRightZero : (l : Zahlen) -> (r : Zahlen) ->
                        (prf : l + r <=> l) -> r <=> 0
plusLeftLeftRightZero (I sl pl) (I sr pr) (ZRefl {prf}) =
    ZRefl {prf = lemma prf}
    where
      lemma : (sl + sr) + pl = sl + (pl + pr) -> sr + 0 = pr
      lemma prf = sym (plusZeroRightNeutral sr) <<=
                  plusRightCancel sr pr pl
                    (
                    plusLeftCancel sl (sr + pl) (pl + pr)
                      (sym (plusAssociative sl sr pl) <<=
                       prf) =>>
                    plusCommutative pl pr
                    )

--------------------------------------------------------------------------------
------------------------  Integer Multiplication Proofs  -----------------------
--------------------------------------------------------------------------------

||| Proof of commutativity of multiplication.
||| @ l left integer
||| @ r right integer
multCommutative : (l : Zahlen) -> (r : Zahlen) -> l * r <=> r * l
multCommutative (I sl pl) (I sr pr) = ZRefl {prf = lemma}
  where
    lemma : ((sl * sr) + (pl * pr)) + ((sr * pl) + (pr * sl)) =
            ((sr * sl) + (pr * pl)) + ((sl * pr) + (pl * sr))
    lemma = plusLeftRight
              (plusLeftRight (multCommutative sl sr) (multCommutative pl pr))
              (plusLeftRight (multCommutative sr pl) (multCommutative pr sl) =>>
                    plusCommutative (pl * sr) (sl * pr))

||| Multiplying integer by 0 on the left yields 0.
multZeroLeftZero : (r : Zahlen) -> 0 * r <=> 0
multZeroLeftZero (I s p) = ZRefl

||| Multiplying integer by 0 on the right yields 0.
multZeroRightZero : (l : Zahlen) -> l * 0 <=> 0
multZeroRightZero l = multCommutative 0 l <<= multZeroLeftZero l

||| One is multiplicative identity on the left.
multOneLeftNeutral : (r : Zahlen) -> 1 * r <=> r
multOneLeftNeutral (I s p) = ZRefl {prf = lemma}
  where
    lemma : ((s + 0) + 0) + p = s + ((p + 0) + 0)
    lemma = plusConstantRight ((s + 0) + 0) (s + (0 + 0)) p
              (sym (plusAssociative s 0 0)) =>>
            sym (plusAssociative s (0 + 0) p) =>>
            plusConstantLeft ((0 + 0) + p) (0 + (0 + p)) s
              (plusAssociative 0 0 p) =>>
            plusConstantLeft (0 + (0 + p)) (0 + (p + 0)) s
              (plusConstantLeft (0 + p) (p + 0) 0
                (plusCommutative 0 p)) =>>
            plusConstantLeft (0 + (p + 0)) ((0 + p) + 0) s
              (plusAssociative 0 p 0) =>>
            plusConstantLeft ((0 + p) + 0) ((p + 0) + 0) s
              (plusConstantRight (0 + p) (p + 0) 0 (plusCommutative 0 p))

||| One is multiplicative identity on the right.
multOneRightNeutral : (l : Zahlen) -> l * 1 <=> l
multOneRightNeutral l = multCommutative 1 l <<= multOneLeftNeutral l

||| Multiplication distributes over successor function by the right
multLeftSuccPlus : (l : Zahlen) -> (r : Zahlen) -> (S l) * r <=> r + (l * r)
multLeftSuccPlus (I sl pl) (I sr pr) = ZRefl {prf = lemma}
  where
    lemma : (((sl + 1) * sr) + (pl * pr)) + (pr + ((sl * pr) + (pl * sr))) =
            (sr + ((sl * sr) + (pl * pr))) + (((sl + 1) * pr) + (pl * sr))
    lemma = plusLeftRight
            (plusConstantRight ((sl + 1) * sr) (sr + (sl * sr)) (pl * pr)
            (multConstantRight (sl + 1) (S sl) sr
                (plusCommutative sl 1 =>>
                  plusOneSucc sl) =>>
             multLeftSuccPlus sl sr) =>>
             sym (plusAssociative sr (sl * sr) (pl * pr)))
             (plusAssociative pr (sl * pr) (pl * sr) =>>
             plusConstantRight (pr + (sl * pr)) ((sl + 1) * pr) (pl * sr)
               (sym (multLeftSuccPlus sl pr) =>>
                multConstantRight (S sl) (sl + 1) pr
                  (sym (plusOneSucc sl) =>>
                plusCommutative 1 sl)))

||| Multiplication distributes over successor function by the left
multRightSuccPlus : (l : Zahlen) -> (r : Zahlen) -> l * S r <=> l + l * r
multRightSuccPlus l r = multCommutative (S r) l <<=
                        multLeftSuccPlus r l =>>
                        plusConstantLeft (r * l) (l * r) l (multCommutative r l)

||| Integer multiplication is associative.
||| @ l left operand
||| @ c center operand
||| @ r right operand
multAssociative : (l : Zahlen) -> (c : Zahlen) -> (r : Zahlen) ->
                  l * (c * r) <=> l * c * r
multAssociative (I sl pl) (I sc pc) (I sr pr) = ZRefl {prf = lemma}
  where
    lemma : ((sl * ((sc * sr) + (pc * pr))) + (pl * ((sc * pr) + (pc * sr)))) +
            ((((sl * sc) + (pl * pc)) * pr) + (((sl * pc) + (pl * sc)) * sr)) =
            ((((sl * sc) + (pl * pc)) * sr) + (((sl * pc) + (pl * sc)) * pr)) +
            ((sl * ((sc * pr) + (pc * sr))) + (pl * ((sc * sr) + (pc * pr))))
    lemma = plusLeftRight
          (
          plusLeftRight
            (
            multDistributesOverPlusRight sl (sc * sr) (pc * pr) =>>
            plusConstantRight (sl * (sc * sr)) ((sl * sc) * sr) (sl * (pc * pr))
              (multAssociative sl sc sr) =>>
            plusConstantLeft (sl * (pc * pr)) ((sl * pc) * pr) ((sl * sc) * sr)
              (multAssociative sl pc pr)
            ) (
            multDistributesOverPlusRight pl (sc * pr) (pc * sr) =>>
            plusConstantRight (pl * (sc * pr)) ((pl * sc) * pr) (pl * (pc * sr))
              (multAssociative pl sc pr) =>>
            plusConstantLeft (pl * (pc * sr)) ((pl * pc) * sr) ((pl * sc) * pr)
              (multAssociative pl pc sr)
            ) =>>
            sym (plusAssociative ((sl * sc) * sr) ((sl * pc) * pr)
              ((pl * sc) * pr + (pl * pc) * sr)) =>>
            plusConstantLeft
              ((sl * pc) * pr + ((pl * sc) * pr + (pl * pc) * sr))
              (((sl * pc) * pr + (pl * sc) * pr) + (pl * pc) * sr)
              ((sl * sc) * sr)
              (plusAssociative ((sl * pc) * pr) ((pl * sc) * pr)
                ((pl * pc) * sr)) =>>
            plusConstantLeft
              (((sl * pc) * pr + (pl * sc) * pr) + (pl * pc) * sr)
              ((pl * pc) * sr + ((sl * pc) * pr + (pl * sc) * pr))
              ((sl * sc) * sr)
              (plusCommutative ((sl * pc) * pr + (pl * sc) * pr)
                ((pl * pc) * sr)) =>>
            plusAssociative ((sl * sc) * sr) ((pl * pc) * sr)
              ((sl * pc) * pr + (pl * sc) * pr) =>>
            plusConstantRight ((sl * sc) * sr + (pl * pc) * sr)
              (((sl * sc) + (pl * pc)) * sr) ((sl * pc) * pr + (pl * sc) * pr)
              (sym (multDistributesOverPlusLeft (sl * sc) (pl * pc) sr)) =>>
            plusConstantLeft ((sl * pc) * pr + (pl * sc) * pr)
              (((sl * pc) + (pl * sc)) * pr) (((sl * sc) + (pl * pc)) * sr)
              (sym (multDistributesOverPlusLeft (sl * pc) (pl * sc) pr))
          ) (
          plusLeftRight
            (
              multDistributesOverPlusLeft (sl * sc) (pl * pc) pr =>>
              plusConstantRight
                ((sl * sc) * pr) (sl * (sc * pr)) ((pl * pc) * pr)
                (sym (multAssociative sl sc pr)) =>>
              plusConstantLeft ((pl * pc) * pr) (pl * (pc * pr))
                (sl * (sc * pr))
                (sym (multAssociative pl pc pr))
            ) (
            multDistributesOverPlusLeft (sl * pc) (pl * sc) sr =>>
            plusConstantRight ((sl * pc) * sr) (sl * (pc * sr)) ((pl * sc) * sr)
              (sym (multAssociative sl pc sr)) =>>
            plusConstantLeft ((pl * sc) * sr) (pl * (sc * sr)) (sl * (pc * sr))
              (sym (multAssociative pl sc sr))
            ) =>>
            sym (plusAssociative (sl * (sc * pr))
              (pl * (pc * pr)) (sl * (pc * sr) + pl * (sc * sr))) =>>
            plusConstantLeft
              ((pl * (pc * pr)) + (sl * (pc * sr) + pl * (sc * sr)))
              ((sl * (pc * sr) + pl * (sc * sr)) + (pl * (pc * pr)))
              (sl * (sc * pr))
              (plusCommutative (pl * (pc * pr))
                (sl * (pc * sr) + pl * (sc * sr))) =>>
            plusConstantLeft
              ((sl * (pc * sr) + pl * (sc * sr)) + pl * (pc * pr))
              (sl * (pc * sr) + (pl * (sc * sr) + pl * (pc * pr)))
              (sl * (sc * pr))
              (sym (plusAssociative (sl * (pc * sr)) (pl * (sc * sr))
                (pl * (pc * pr)))) =>>
            plusAssociative (sl * (sc * pr)) (sl * (pc * sr))
              (pl * (sc * sr) + pl * (pc * pr)) =>>
            plusConstantRight (sl * (sc * pr) + sl * (pc * sr))
              (sl * ((sc * pr) + (pc * sr)))
              (pl * (sc * sr) + pl * (pc * pr))
              (sym (multDistributesOverPlusRight sl (sc * pr) (pc * sr))) =>>
            plusConstantLeft (pl * (sc * sr) + pl * (pc * pr))
              (pl * ((sc * sr) + (pc * pr))) (sl * ((sc * pr) + (pc * sr)))
              (sym (multDistributesOverPlusRight pl (sc * sr) (pc * pr)))
        )

||| Multiplication distributes over addition by the right
||| @ l left multiplicand
||| @ c left addend
||| @ r right addend
multDistributesOverPlusRight : (l : Zahlen) -> (c : Zahlen) -> (r : Zahlen) ->
                               l * (c + r) <=> (l * c) + (l * r)
multDistributesOverPlusRight (I sl pl) (I sc pc) (I sr pr) =
  ZRefl {prf = lemma}
  where
    lemma : ((sl * (sc + sr)) + (pl * (pc + pr))) +
            (((sl * pc) + (pl * sc)) + ((sl * pr) + (pl * sr))) =
            (((sl * sc) + (pl * pc)) + ((sl * sr) + (pl * pr))) +
            ((sl * (pc + pr)) + (pl * (sc + sr)))
    lemma = plusLeftRight
          (plusLeftRight (multDistributesOverPlusRight sl sc sr)
            (multDistributesOverPlusRight pl pc pr) =>>
          sym (plusAssociative (sl * sc) (sl * sr) ((pl * pc) + (pl * pr))) =>>
          plusConstantLeft ((sl * sr) + ((pl * pc) + (pl * pr)))
            (((sl * sr) + (pl * pc)) + (pl * pr)) (sl * sc)
            (plusAssociative (sl * sr) (pl * pc) (pl * pr)) =>>
          plusConstantLeft (((sl * sr) + (pl * pc)) + (pl * pr))
            (((pl * pc) + (sl * sr)) + (pl * pr)) (sl * sc)
            (plusConstantRight ((sl * sr) + (pl * pc)) ((pl * pc) + (sl * sr))
              (pl * pr) (plusCommutative (sl * sr) (pl * pc))) =>>
          plusAssociative (sl * sc) ((pl * pc) + (sl * sr)) (pl * pr) =>>
          plusConstantRight ((sl * sc) + ((pl * pc) + (sl * sr)))
            (((sl * sc) + (pl * pc)) + (sl * sr)) (pl * pr)
            (plusAssociative (sl * sc) (pl * pc) (sl * sr)) =>>
          sym (plusAssociative ((sl * sc) + (pl * pc)) (sl * sr) (pl * pr)))
          (sym (plusAssociative (sl * pc) (pl * sc) ((sl * pr) + (pl * sr))) =>>
          plusConstantLeft ((pl * sc) + ((sl * pr) + (pl * sr)))
            (((pl * sc) + (sl * pr)) + (pl * sr)) (sl * pc)
            (plusAssociative (pl * sc) (sl * pr) (pl * sr)) =>>
          plusConstantLeft (((pl * sc) + (sl * pr)) + (pl * sr))
            (((sl * pr) + (pl * sc)) + (pl * sr)) (sl * pc)
            (plusConstantRight ((pl * sc) + (sl * pr)) ((sl * pr) + (pl * sc))
              (pl * sr) (plusCommutative (pl * sc) (sl * pr))) =>>
          plusAssociative (sl * pc) ((sl * pr) + (pl * sc)) (pl * sr) =>>
          plusConstantRight ((sl * pc) + ((sl * pr) + (pl * sc)))
            (((sl * pc) + (sl * pr)) + (pl * sc)) (pl * sr)
            (plusAssociative (sl * pc) (sl * pr) (pl * sc)) =>>
          sym (plusAssociative ((sl * pc) + (sl * pr)) (pl * sc) (pl * sr)) =>>
          plusConstantRight ((sl * pc) + (sl * pr)) (sl * (pc + pr))
            ((pl * sc) + (pl * sr))
            (sym (multDistributesOverPlusRight sl pc pr)) =>>
          plusConstantLeft ((pl * sc) + (pl * sr)) (pl * (sc + sr))
            (sl * (pc + pr)) (sym (multDistributesOverPlusRight pl sc sr)))

||| Multiplication distributes over addition function by the left
||| @ l left addend
||| @ c right addend
||| @ r right multiplicand
multDistributesOverPlusLeft : (l : Zahlen) -> (c : Zahlen) -> (r : Zahlen) ->
                              (l + c) * r <=> (l * r) + (c * r)
multDistributesOverPlusLeft l c r = multCommutative r (l + c) <<=
                                    multDistributesOverPlusRight r l c =>>
                                    plusConstantRight (r * l) (l * r) (r * c)
                                      (multCommutative r l) =>>
                                    plusConstantLeft (r * c) (c * r) (l * r)
                                      (multCommutative r c)

namespace ZahlenmultConstantRight
  ||| Equiv is invariant upon multiplying constants to the right.
  ||| @ l natural to the left of equality
  ||| @ r natural to the right of equality
  ||| @ c constant to be added
  ||| @ prf proof that l <=> r
  multConstantRight : (l : Zahlen) -> (r : Zahlen) -> (c : Zahlen) ->
                      (prf : l <=> r) -> l * c <=> r * c
  multConstantRight (I sl pl) (I sr pr) (I sc pc) (ZRefl {prf = prf}) =
    ZRefl {prf = lemma prf}
    where
      lemma : (sl + pr) = (sr + pl) ->
              ((sl * sc) + (pl * pc)) + ((sr * pc) + (pr * sc)) =
              ((sr * sc) + (pr * pc)) + ((sl * pc) + (pl * sc))
      lemma prf =
            sym (plusAssociative (sl * sc) (pl * pc) ((sr * pc) + (pr * sc))) =>>
            plusConstantLeft ((pl * pc) + ((sr * pc) + (pr * sc)))
              ((pr * sc)  + ((pl + sr) * pc)) (sl * sc)
              (plusAssociative (pl * pc) (sr * pc) (pr * sc) =>>
              plusConstantRight ((pl * pc) + (sr * pc)) ((pl + sr) * pc)
                (pr * sc) (sym (multDistributesOverPlusLeft pl sr pc)) =>>
              plusCommutative ((pl + sr) * pc) (pr * sc)) =>>
            plusAssociative (sl * sc) (pr * sc) ((pl + sr) * pc) =>>
            plusConstantRight ((sl * sc) + (pr * sc)) ((sl + pr) * sc)
              ((pl + sr) * pc) (sym (multDistributesOverPlusLeft sl pr sc)) =>>
            plusLeftRight (multConstantRight (sl + pr) (sr + pl) sc prf)
              (multConstantRight (pl + sr) (sl + pr) pc
              (plusCommutative pl sr =>> sym prf)) =>>
            plusLeftRight (multDistributesOverPlusLeft sr pl sc)
              (multDistributesOverPlusLeft sl pr pc =>>
              plusCommutative (sl * pc) (pr * pc)) =>>
            sym (plusAssociative (sr * sc) (pl * sc) (pr * pc + sl * pc)) =>>
            plusConstantLeft (pl * sc + (pr * pc + sl * pc))
              (pr * pc + (pl * sc + sl * pc)) (sr * sc)
              (plusAssociative (pl * sc) (pr * pc) (sl * pc) =>>
                plusConstantRight (pl * sc + pr * pc) (pr * pc + pl * sc)
                  (sl * pc) (plusCommutative (pl * sc) (pr * pc)) =>>
                sym (plusAssociative (pr * pc) (pl * sc) (sl * pc))) =>>
            plusAssociative (sr * sc) (pr * pc) (pl * sc + sl * pc) =>>
            plusConstantLeft (pl * sc + sl * pc) (sl * pc + pl * sc)
              (sr * sc + pr * pc) (plusCommutative (pl * sc) (sl * pc))

  ||| Equiv is invariant upon multiplying constants to the left.
  ||| @ l natural to the left of equality
  ||| @ r natural to the right of equality
  ||| @ c constant to be added
  ||| @ prf proof that l <=> r
  multConstantLeft : (l : Zahlen) -> (r : Zahlen) -> (c : Zahlen) ->
                      (prf : l <=> r) -> c * l <=> c * r
  multConstantLeft l r c prf = multCommutative l c <<=
                               multConstantRight l r c prf =>>
                               multCommutative r c

--------------------------------------------------------------------------------
----------------------------  Integer Minus Proofs  ----------------------------
--------------------------------------------------------------------------------

negateCancel : (l : Zahlen) -> (r : Zahlen) -> negate l <=> negate r -> l <=> r
negateCancel (I sl pl) (I sr pr) (ZRefl {prf}) = ZRefl {prf = lemma prf}
  where
    lemma : pl + sr = pr + sl -> sl + pr = sr + pl
    lemma prf = plusCommutative pr sl <<= sym prf =>> plusCommutative pl sr

minusSuccSucc : (l : Zahlen) -> (r : Zahlen) -> (S l) - (S r) <=> l - r
minusSuccSucc (I sl pl) (I sr pr) = ZRefl {prf = lemma}
  where
    lemma : ((sl + 1) + pr) + (pl + sr) = (sl + pr) + (pl + (sr + 1))
    lemma = plusConstantRight ((sl + 1) + pr) ((sl + pr) + 1) (pl + sr)
            (sym (plusAssociative sl 1 pr) =>>
          plusConstantLeft (1 + pr) (pr + 1) sl (plusCommutative 1 pr) =>>
          plusAssociative sl pr 1) =>>
          sym (plusAssociative (sl + pr) 1 (pl + sr)) =>>
          plusConstantLeft (1 + (pl + sr)) (pl + (sr + 1)) (sl + pr)
            (plusCommutative 1 (pl + sr) =>> sym (plusAssociative pl sr 1))

minusPredPred : (l : Zahlen) -> (r : Zahlen) -> (P l) - (P r) <=> l - r
minusPredPred (I sl pl) (I sr pr) = ZRefl {prf = lemma}
  where
    lemma : (sl + (pr + 1)) + (pl + sr) = (sl + pr) + ((pl + 1) + sr)
    lemma = plusConstantRight (sl + (pr + 1)) ((sl + pr) + 1) (pl + sr)
            (plusAssociative sl pr 1) =>>
          sym (plusAssociative (sl + pr) 1 (pl + sr)) =>>
          plusConstantLeft (1 + (pl + sr)) ((pl + 1) + sr) (sl + pr)
            (plusAssociative 1 pl sr =>>
            plusConstantRight (1 + pl) (pl + 1) sr (plusCommutative 1 pl))

minusOnePred : (z : Zahlen) -> z - 1 <=> P z
minusOnePred (I s p) = ZRefl {prf = lemma}
  where
    lemma : (s + 0) + (p + 1) = s + (p + 1)
    lemma = plusConstantRight (s + 0) s (p + 1) (plusZeroRightNeutral s)

minusZeroLeft : (r : Zahlen) -> 0 - r <=> negate r
minusZeroLeft (I s p) = ZRefl

minusZeroRight : (l : Zahlen) -> l - 0 <=> l
minusZeroRight (I s p) = ZRefl {prf = lemma}
  where
    lemma : (s + 0) + p = s + (p + 0)
    lemma = sym (plusAssociative s 0 p) =>>
            plusConstantLeft (0 + p) (p + 0) s (plusCommutative 0 p)

minusZeroN : (z : Zahlen) -> 0 <=> z - z
minusZeroN (I s p) = ZRefl {prf = lemma}
  where
    lemma : p + s = (s + p) + 0
    lemma = plusCommutative p s =>>
            sym (plusZeroRightNeutral (s + p))

minusOneSuccN : (z : Zahlen) -> 1 <=> (S z) - z
minusOneSuccN (I s p) = ZRefl {prf = lemma}
  where
    lemma : S (p + s) = ((s + 1) + p) + 0
    lemma = sym (plusOneSucc (p + s)) =>>
            plusConstantLeft (p + s) (s + p) 1 (plusCommutative p s) =>>
            plusAssociative 1 s p =>>
            plusConstantRight (1 + s) (s + 1) p (plusCommutative 1 s) =>>
            sym (plusZeroRightNeutral ((s + 1) + p))

minusSuccOne : (z: Zahlen) -> (S z) - 1 <=> z
minusSuccOne (I s p) = ZRefl {prf = lemma}
  where
    lemma : ((s + 1) + 0) + p = s + (p + 1)
    lemma = plusConstantRight ((s + 1) + 0) (s + 1) p
              (plusZeroRightNeutral (s + 1)) =>>
            sym (plusAssociative s 1 p) =>>
            plusConstantLeft (1 + p) (p + 1) s (plusCommutative 1 p)

minusPlusCancel : (n : Zahlen) -> (m : Zahlen) -> n - (n + m) <=> negate m
minusPlusCancel (I sn pn) (I sm pm) = ZRefl {prf = lemma}
  where
    lemma : (sn + (pn + pm)) + sm = pm + (pn + (sn + sm))
    lemma = plusConstantRight (sn + (pn + pm)) (pm + (pn + sn)) sm
            (plusCommutative sn (pn + pm) =>>
            plusConstantRight (pn + pm) (pm + pn) sn
              (plusCommutative pn pm) =>>
            sym (plusAssociative pm pn sn)) =>>
          sym (plusAssociative pm (pn + sn) sm) =>>
          plusConstantLeft ((pn + sn) + sm) (pn + (sn + sm)) pm
            (sym (plusAssociative pn sn sm))


minusAntiCommutative : (l : Zahlen) -> (r : Zahlen) -> l - r <=> negate (r - l)
minusAntiCommutative (I sl pl) (I sr pr) =
  ZRefl {prf = plusLeftRight (plusCommutative sl pr) (plusCommutative sr pl)}

minusMinusMinusPlus : (l : Zahlen) -> (c : Zahlen) -> (r : Zahlen) ->
                      (l - c) - r <=> l - (c + r)
minusMinusMinusPlus (I sl pl) (I sc pc) (I sr pr) = ZRefl
  {prf = plusLeftRight (sym (plusAssociative sl pc pr))
                       (plusAssociative pl sc sr)}

minusConstantRight : (l : Zahlen) -> (r : Zahlen) -> (c : Zahlen) ->
                   l <=> r -> l - c <=> r - c
minusConstantRight (I sl pl) (I sr pr) (I sc pc) (ZRefl {prf}) = ZRefl {prf = lemma prf}
  where
    lemma : sl + pr = sr + pl -> (sl + pc) + (pr + sc) = (sr + pc) + (pl + sc)
    lemma prf = sym (plusAssociative sl pc (pr + sc)) =>>
                plusConstantLeft (pc + (pr + sc)) ((pr + pc) + sc) sl
                  (plusAssociative pc pr sc =>>
                  plusConstantRight (pc + pr) (pr + pc) sc (plusCommutative pc pr)) =>>
                plusAssociative sl (pr + pc) sc =>>
                plusConstantRight (sl + (pr + pc)) ((sl + pr) + pc) sc
                  (plusAssociative sl pr pc) =>>
                plusConstantRight ((sl + pr) + pc) ((sr + pl) + pc) sc
                  (plusConstantRight (sl + pr) (sr + pl) pc prf) =>>
                plusConstantRight ((sr + pl) + pc) ((sr + pc) + pl) sc
                  (sym (plusAssociative sr pl pc) =>>
                  plusConstantLeft (pl + pc) (pc + pl) sr (plusCommutative pl pc) =>>
                  plusAssociative sr pc pl) =>>
                sym (plusAssociative (sr + pc) pl sc)

minusConstantLeft : (l : Zahlen) -> (r : Zahlen) -> (c : Zahlen) ->
                   l <=> r -> c - l <=> c - r
minusConstantLeft l r c prf = lemma
  where
    lemma : c - l <=> c - r
    lemma = negateCancel (c - l) (c - r)
            (minusAntiCommutative l c <<=
            minusConstantRight l r c prf =>>
            minusAntiCommutative r c)

minusLeftRight : {l1, l2, r1, r2 : Zahlen} ->
                 l1 <=> l2 -> r1 <=> r2 -> l1 - r1 <=> l2 - r2
minusLeftRight {l1} {l2} {r1} {r2} prf1 prf2 =
  minusConstantRight l1 l2 r1 prf1 =>> minusConstantLeft r1 r2 l2 prf2

plusMinusLeftCancel : (l : Zahlen) -> (r : Zahlen) -> (r' : Zahlen) ->
                      (l + r) - (l + r') <=> r - r'
plusMinusLeftCancel (I sl pl) (I sr pr) (I sr' pr') = ZRefl {prf = lemma}
  where
    lemma : ((sl + sr) + (pl + pr')) + (pr + sr') =
            (sr + pr') + ((pl + pr) + (sl + sr'))
    lemma = plusConstantRight ((sl + sr) + (pl + pr')) ((sr + pr') + (sl + pl))
            (pr + sr')
            (plusLeftRight (plusCommutative sl sr) (plusCommutative pl pr') =>>
            sym (plusAssociative sr sl (pr' + pl)) =>>
            plusConstantLeft (sl + (pr' + pl)) ((pr' + sl) + pl) sr
              (plusAssociative sl pr' pl =>>
              plusConstantRight (sl + pr') (pr' + sl) pl
                (plusCommutative sl pr')) =>>
            plusAssociative sr (pr' + sl) pl =>>
            plusConstantRight (sr + (pr' + sl)) ((sr + pr') + sl) pl
              (plusAssociative sr pr' sl) =>>
            sym (plusAssociative (sr + pr') sl pl)) =>>
            sym (plusAssociative (sr + pr') (sl + pl) (pr + sr')) =>>
            plusConstantLeft ((sl + pl) + (pr + sr')) ((pl + pr) + (sl + sr'))
              (sr + pr')
              (sym (plusAssociative sl pl (pr + sr')) =>>
              plusConstantLeft (pl + (pr + sr')) (sr' + (pl + pr)) sl
                (plusAssociative pl pr sr' =>>
                  plusCommutative (pl + pr) sr') =>>
              plusAssociative sl sr' (pl + pr) =>>
              plusCommutative (sl + sr') (pl + pr))

plusMinusRightCancel : (l : Zahlen) -> (l' : Zahlen) -> (r : Zahlen) ->
                      (l + r) - (l' + r) <=> l - l'
plusMinusRightCancel l l' r =
  minusLeftRight (plusCommutative r l) (plusCommutative r l') <<=
  plusMinusLeftCancel r l l'

multDistributesOverMinusLeft : (l : Zahlen) -> (c : Zahlen) -> (r : Zahlen) ->
                               (l - c) * r <=> (l * r) - (c * r)
multDistributesOverMinusLeft (I sl pl) (I sc pc) (I sr pr) = ZRefl {prf = lemma}
  where
    lemma : (((sl + pc) * sr) + ((pl + sc) * pr)) +
            (((sl * pr) + (pl * sr)) + ((sc * sr) + (pc * pr))) =
            (((sl * sr) + (pl * pr)) + ((sc * pr) + (pc * sr))) +
            (((sl + pc) * pr) + ((pl + sc) * sr))
    lemma = plusLeftRight
              (plusLeftRight (multDistributesOverPlusLeft sl pc sr)
                (multDistributesOverPlusLeft pl sc pr) =>>
              sym (plusAssociative (sl * sr) (pc * sr)
                ((pl * pr) + (sc * pr))) =>>
              plusConstantLeft ((pc * sr) + ((pl * pr) + (sc * pr)))
                ((pl * pr) + ((sc * pr) + (pc * sr))) (sl * sr)
                  (plusCommutative (pc * sr) ((pl * pr) + (sc * pr)) =>>
                  sym (plusAssociative (pl * pr) (sc * pr) (pc * sr))) =>>
              plusAssociative (sl * sr) (pl * pr) ((sc * pr) + (pc * sr)))
              (plusConstantLeft ((sc * sr) + (pc * pr)) ((pc * pr) + (sc * sr))
                ((sl * pr) + (pl * sr))
                (plusCommutative (sc * sr) (pc * pr)) =>>
              sym (plusAssociative (sl * pr) (pl * sr)
                ((pc * pr) + (sc * sr))) =>>
              plusConstantLeft ((pl * sr) + ((pc * pr) + (sc * sr)))
               ((pc * pr) + ((pl * sr) + (sc * sr))) (sl * pr)
                  (plusAssociative (pl * sr) (pc * pr) (sc * sr) =>>
                  plusConstantRight ((pl * sr) + (pc * pr))
                    ((pc * pr) + (pl * sr))
                    (sc * sr) (plusCommutative (pl * sr) (pc * pr)) =>>
                  sym (plusAssociative (pc * pr) (pl * sr) (sc * sr))) =>>
              plusAssociative (sl * pr) (pc * pr) ((pl * sr) + (sc * sr)) =>>
              plusConstantRight ((sl * pr) + (pc * pr)) ((sl + pc) * pr)
                ((pl * sr) + (sc * sr))
                (sym (multDistributesOverPlusLeft sl pc pr)) =>>
              plusConstantLeft ((pl * sr) + (sc * sr))
                ((pl + sc) * sr) ((sl + pc) * pr)
                (sym (multDistributesOverPlusLeft pl sc sr)))

multDistributesOverMinusRight : (l : Zahlen) -> (c : Zahlen) -> (r : Zahlen) ->
                                l * (c - r) <=> (l * c) - (l * r)
multDistributesOverMinusRight l c r = lemma
  where
    lemma : l * (c - r) <=> (l * c) - (l * r)
    lemma = multCommutative (c - r) l <<=
            multDistributesOverMinusLeft c r l =>>
            minusLeftRight (multCommutative c l) (multCommutative r l)

--------------------------------------------------------------------------------
----------------------------------  Division  ----------------------------------
--------------------------------------------------------------------------------
{- Implementations are not total due to 0 -}

notZero : {s, p : Nat} -> {auto prf : Not (s = p)} -> Not ((I s p) <=> 0)
notZero {s} {p} {prf = prf} = lemma
  where
    lemma : Equiv (I s p) 0 -> Void
    lemma (ZRefl {prf = equ}) =
      prf (rewrite sym (plusZeroRightNeutral s) in equ)

||| Unsafe mod function (creates infinite loop at 0)
partial
modInt : Zahlen -> Zahlen -> Zahlen
modInt l r = if lt l 0 then
              (abs r) - (modInt (negate l) r)
             else if lt r 0 then
              mod' l l (negate r)
             else
              mod' l l r
  where
    partial
    mod' : Zahlen -> Zahlen -> Zahlen -> Zahlen
    mod' l c r =
      if lt c r then
        c
      else
    mod' l (c - r) r

||| Unsafe div function (creates infinite loop at 0)
partial
divInt : Zahlen -> Zahlen -> Zahlen
divInt l r = if lt l 0 then
              (negate (divInt (negate l) r))
             else if lt r 0 then
              negate (div' l l (negate r))
             else
              div' l l r
  where
    partial
    div' : Zahlen -> Zahlen -> Zahlen -> Zahlen
    div' l c r =
      if lt c r then
        Z
      else
        S (div' l (c - r) r)

||| Implemantation of Zahlen as Integral type.
partial
Integral Zahlen where
  div l r = divInt l r
  mod l r = modInt l r
