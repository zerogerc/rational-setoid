module RationalSetoid

import Setoid
import IntegerSetoid
import CustomIntAxioms

%access public export

record CustomRat where
  constructor MkCustomRat
  num : CustomInt
  denum : CustomInt
  notZero : (Not (denum :=: 0))

-- implementation Num CustomRat where
--   (+) (MkCustomRat a b) (MkCustomRat c d) =
--     MkCustomRat ((a * d) + (c * b)) (b * d)
--
--   (*) (MkCustomRat a b) (MkCustomRat c d) =
--     MkCustomRat (a * c) (b * d)
--
--   fromInteger n =
--     if n > 0
--         then MkCustomRat (MkCustomInt (fromInteger n) Z) $ MkCustomInt 1 Z
--         else MkCustomRat (MkCustomInt Z (fromInteger $ abs n)) $ MkCustomInt 1 Z
--
-- implementation Neg CustomRat where
--   negate (MkCustomRat (MkCustomInt a b) c) =
--     MkCustomRat (MkCustomInt b a) c
--
--   (-) n (MkCustomRat a b) = n + (MkCustomRat (negate a) b)
--
--   abs (MkCustomRat a b) =
--     MkCustomRat (abs a) $ abs b
--
-- implementation Fractional CustomRat where
--     (/) a b = a * (recip b)
--     recip (MkCustomRat a b) = (MkCustomRat b a)


-- data CustomRatEq : CustomRat -> CustomRat -> Type where
--   MkCustomRatEq : {a : CustomInt} -> {b : CustomInt} -> {c : CustomInt} -> {d : CustomInt}
--     -> (a * d = c * b) -> CustomRatEq (MkCustomRat a b) (MkCustomRat c d)
--
-- customRatRefl : Reflx CustomRatEq
-- customRatRefl (MkCustomRat a b) =
--   MkCustomRatEq Refl
--
-- customRatSym : Sym CustomRatEq
-- customRatSym (MkCustomRat a b) (MkCustomRat c d) (MkCustomRatEq eq) =
--   MkCustomRatEq $ sym eq
--
-- customRatTrans : Trans CustomRatEq
-- customRatTrans (MkCustomRat a b) (MkCustomRat c d) (MkCustomRat e f)
--   (MkCustomRatEq eq1) (MkCustomRatEq eq2) = let
--     -- result : a * f = e * b
--     -- eq3 : (a * d) * (c * f) = (c * b) * (e * d)
--     eq3 = intEqAdditionRefl eq1 eq2
--     eliminateD1 = intMultCommutative (a * d) (c * f)
--     in ?asfas
--
-- CustomRatSetoid : Setoid
-- CustomRatSetoid = MkSetoid CustomRat CustomRatEq $ EqProof CustomRatEq customRatRefl customRatSym customRatTrans
