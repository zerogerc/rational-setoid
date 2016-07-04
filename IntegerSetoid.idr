module IntegerSetoid
import Setoid

%access public export

record CustomInt where
    constructor MkCustomInt
    first : Nat
    second : Nat

implementation Num CustomInt where
  (+) (MkCustomInt a b) (MkCustomInt c d) = MkCustomInt (a + c) (b + d)

  (*) (MkCustomInt a b) (MkCustomInt c d) = MkCustomInt (a * c + b * d) (a * d + b * c)

  fromInteger n =
    if n > 0
      then MkCustomInt (fromInteger n) Z
      else MkCustomInt Z (fromInteger $ abs n)

implementation Neg CustomInt where
  negate (MkCustomInt a b) = MkCustomInt b a
  (-) (MkCustomInt a b) (MkCustomInt c d) = MkCustomInt (a + d) (b + c)
  abs (MkCustomInt a b) =
    if a > b
      then (MkCustomInt a b)
      else (MkCustomInt b a)


data CustomIntEq : CustomInt -> CustomInt -> Type where
    MkCustomIntEq : {x : CustomInt} -> {y : CustomInt}
      -> {eq : (first x) + (second y) = (first y) + (second x)}
      -> CustomIntEq x y

eqAdditionRefl : {a : Nat} -> {b : Nat} -> {c : Nat} -> {d : Nat} -> (a = b) -> (c = d) -> (a + c = b + d)
eqAdditionRefl eq1 eq2 = rewrite eq1 in rewrite eq2 in Refl

customIntTrans : {a, b, c, d, e, f : Nat} -> (a + d = c + b) -> (c + f = e + d) -> (a + f = e + b)
customIntTrans {a} {b} {c} {d} {e} {f} eq1 eq2 = let
  eq3 = eqAdditionRefl eq1 eq2
  eliminateD1 = plusCommutative (a + d) (c + f)
  eliminateD2 = plusAssociative (c + f) a d
  eliminateD3 = plusAssociative (c + b) e d
  eliminateD4 = trans (sym eliminateD2) $ trans (sym eliminateD1) $ trans eq3 eliminateD3
  eliminateD = plusRightCancel ((c + f) + a) ((c + b) + e) d eliminateD4
  eliminateC1 = trans (plusAssociative c f a) eliminateD
  eliminateC2 = trans (plusAssociative c b e) (sym eliminateD)
  eliminateC3 = trans eliminateC1 $ sym $ trans eliminateC2 eliminateD
  eliminateC4 = plusLeftCancel c (f + a) (b + e) eliminateC3
  eliminateC5 = trans eliminateC4 $ plusCommutative b e
  eliminateC6 = trans (plusCommutative a f) eliminateC5
  in eliminateC6

implementation Setoid CustomInt where
  (:=:) = CustomIntEq
  Reflx a = MkCustomIntEq {eq = Refl}
  Sym a b ( MkCustomIntEq {eq = abEq} ) = MkCustomIntEq {eq = sym abEq}
  Trans a b c (MkCustomIntEq {eq=eq1}) (MkCustomIntEq {eq=eq2}) = MkCustomIntEq {eq=customIntTrans eq1 eq2}
