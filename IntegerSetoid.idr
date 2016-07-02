module IntegerSetoid
import Setoid
%access public export

data CustomInt = MkCustomInt Nat Nat

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
  MkCustomIntEq : {a : Nat} -> {b : Nat} -> {c : Nat} -> {d : Nat}
    -> (eq : a + d = c + b) -> CustomIntEq (MkCustomInt a b) (MkCustomInt c d)

customIntReflx : Reflx CustomIntEq
customIntReflx (MkCustomInt a b) = MkCustomIntEq Refl

customIntSym : Sym CustomIntEq
customIntSym (MkCustomInt a b) (MkCustomInt c d) (MkCustomIntEq eq) =
  MkCustomIntEq $ sym eq

eqAdditionRefl : {a : Nat} -> {b : Nat} -> {c : Nat} -> {d : Nat} -> (a = b) -> (c = d) -> (a + c = b + d)
eqAdditionRefl eq1 eq2 = rewrite eq1 in rewrite eq2 in Refl

customIntTrans : Trans CustomIntEq
customIntTrans (MkCustomInt a b) (MkCustomInt c d) (MkCustomInt e f)
  (MkCustomIntEq eq1) (MkCustomIntEq eq2) = let
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
  in MkCustomIntEq eliminateC6

CustomIntSetoid : Setoid
CustomIntSetoid = MkSetoid CustomInt CustomIntEq $ EqProof CustomIntEq customIntReflx customIntSym customIntTrans
