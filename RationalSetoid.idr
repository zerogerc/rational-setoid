module RationalSetoid

import Setoid
import IntegerSetoid

%access public export

data CustomRat = MkCustomRat CustomInt CustomInt

implementation Num CustomRat where
  (+) (MkCustomRat a b) (MkCustomRat c d) =
    MkCustomRat ((a * d) + (c * b)) (b * d)

  (*) (MkCustomRat a b) (MkCustomRat c d) =
    MkCustomRat (a * c) (b * d)

  fromInteger n =
    if n > 0
        then MkCustomRat (MkCustomInt (fromInteger n) Z) $ MkCustomInt 1 Z
        else MkCustomRat (MkCustomInt Z (fromInteger $ abs n)) $ MkCustomInt 1 Z

implementation Neg CustomRat where
  negate (MkCustomRat (MkCustomInt a b) c) =
    MkCustomRat (MkCustomInt b a) c

  (-) n (MkCustomRat a b) = n + (MkCustomRat (negate a) b)

  abs (MkCustomRat a b) =
    MkCustomRat (abs a) $ abs b

implementation Fractional CustomRat where
    (/) a b = a * (recip b)
    recip (MkCustomRat a b) = (MkCustomRat b a)
