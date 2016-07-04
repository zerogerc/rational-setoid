module CustomIntAxioms.idr
import Setoid
import IntegerSetoid

%access public export

lemma1 : (a,b,c,d,e,f : Nat) -> (a * c * e + a * d * f + b * d * e) = (a * c * e + b * d * e + a * d * f)
lemma1 a b c d e f =
  rewrite sym $ plusAssociative (a * c * e) (a * d * f) (b * d * e)
  in rewrite sym $ plusAssociative (a * c * e) (b * d * e) (a * d * f)
  in rewrite plusCommutative (a * d * f) (b * d * e)
  in Refl

lemma2 : (a,b,c,d,e,f : Nat)
  -> (a * c * e + a * d * f) + (b * c * f + b * d * e) = (a * c * e + b * d * e) + (a * d * f + b * c * f)
lemma2 a b c d e f =
  rewrite plusCommutative (b * c * f) (b * d * e)
  in rewrite plusAssociative (a * c * e + a * d * f) (b * d * e) (b * c * f)
  in rewrite plusAssociative (a * c * e + b * d * e) (a * d * f) (b * c * f)
  in rewrite lemma1 a b c d e f
  in Refl

lemma3 : (a, b, c, d, e, f : Nat)
  -> (a * c * f + b * d * f + a * d * e) = (a * c * f + a * d * e + b * d * f)
lemma3 a b c d e f = rewrite sym $ plusAssociative (a * c * f) (b * d * f) (a * d * e)
in rewrite sym $ plusAssociative (a * c * f) (a * d * e) (b * d * f)
in rewrite plusCommutative (b * d * f) (a * d * e)
in Refl

lemma4 : (a, b, c, d, e, f : Nat)
  -> (a * c * f + b * d * f) + (a * d * e + b * c * e) = (a * c * f + a * d * e) + (b * c * e + b * d * f)
lemma4 a b c d e f =
  rewrite plusCommutative (b * c * e) (b * d * f)
  in rewrite plusAssociative (a * c * f + b * d * f) (a * d * e) (b * c * e)
  in rewrite plusAssociative (a * c * f + a * d * e) (b * d * f) (b * c * e)
  in rewrite lemma3 a b c d e f
  in Refl

lemma5 : (a, b, c, d, e, f : Nat)
  -> (a * c + a * e) + (b * d + b * f) = (a * c + b * d) + (a * e + b * f)
lemma5 a b c d e f =
  rewrite plusAssociative (a * c + a * e) (b * d) (b * f)
  in rewrite plusAssociative (a * c + b * d) (a * e) (b * f)
  in rewrite sym $ plusAssociative (a * c) (a * e) (b * d)
  in rewrite plusCommutative (a * e) (b * d)
  in rewrite plusAssociative (a * c) (b * d) (a * e)
  in Refl

lemma6 : (a, b, c, d, e, f : Nat)
  -> (a * e + c * e) + (b * f + d * f) = (a * e + b * f) + (c * e + d * f)
lemma6 a b c d e f =
  rewrite plusAssociative (a * e + c * e) (b * f) (d * f)
  in rewrite plusAssociative (a * e + b * f) (c * e) (d * f)
  in rewrite sym $ plusAssociative (a * e) (c * e) (b * f)
  in rewrite plusCommutative (c * e) (b * f)
  in rewrite plusAssociative (a * e) (b * f) (c * e)
  in Refl

implementation Ring CustomInt where

  PlusComm (MkCustomInt a b) (MkCustomInt c d) = MkCustomIntEq {
    eq = rewrite plusCommutative a c
    in rewrite plusCommutative d b
    in Refl
  }

  PlusAssoc (MkCustomInt a b) (MkCustomInt c d) (MkCustomInt e f) = MkCustomIntEq {
    eq = rewrite plusAssociative a c e
    in rewrite plusAssociative b d f
    in Refl
  }

  Zero = 0

  ZeroNeutral (MkCustomInt a b) = MkCustomIntEq {
    eq = rewrite (plusZeroRightNeutral a)
    in rewrite (plusZeroRightNeutral b)
    in Refl
  }

  NegateEx (MkCustomInt a b) = MkCustomIntEq {
    eq = rewrite plusZeroRightNeutral (a + b)
    in (plusCommutative a b)
  }

  MultComm (MkCustomInt a b) (MkCustomInt c d) = MkCustomIntEq {
    eq = rewrite multCommutative a c
    in rewrite multCommutative b d
    in rewrite multCommutative c b
    in rewrite multCommutative d a
    in rewrite plusCommutative (b * c) (a * d)
    in Refl
  }

  MultAssoc (MkCustomInt a b) (MkCustomInt c d) (MkCustomInt e f) = MkCustomIntEq {
    eq =
    rewrite multDistributesOverPlusRight a (c * e) (d * f)
    in rewrite multDistributesOverPlusRight b (c * f) (d * e)
    in rewrite multDistributesOverPlusLeft (a * c) (b * d) e
    in rewrite multDistributesOverPlusLeft (a * d) (b * c) f
    in rewrite multAssociative a c e
    in rewrite multAssociative a d f
    in rewrite multAssociative b c f
    in rewrite multAssociative b d e
    in rewrite lemma2 a b c d e f
    in rewrite multDistributesOverPlusRight a (c * f) (d * e)
    in rewrite multDistributesOverPlusRight b (c * e) (d * f)
    in rewrite multDistributesOverPlusLeft (a * c) (b * d) f
    in rewrite multDistributesOverPlusLeft (a * d) (b * c) e
    in rewrite multAssociative a c f
    in rewrite multAssociative a d e
    in rewrite multAssociative b c e
    in rewrite multAssociative b d f
    in rewrite lemma4 a b c d e f
    in Refl
  }

  MultDistrLeft (MkCustomInt a b) (MkCustomInt c d) (MkCustomInt e f) = MkCustomIntEq {
    eq = rewrite multDistributesOverPlusRight a c e
    in rewrite multDistributesOverPlusRight b d f
    in rewrite multDistributesOverPlusRight a d f
    in rewrite multDistributesOverPlusRight b c e
    in rewrite lemma5 a b c d e f
    in rewrite lemma5 a b d c f e
    in Refl
  }

  MultDistrRight (MkCustomInt a b) (MkCustomInt c d) (MkCustomInt e f) = MkCustomIntEq {
    eq = rewrite multDistributesOverPlusLeft a c e
    in rewrite multDistributesOverPlusLeft b d f
    in rewrite multDistributesOverPlusLeft a c f
    in rewrite multDistributesOverPlusLeft b d e
    in rewrite lemma6 a b c d e f
    in rewrite lemma6 a b c d f e
    in Refl
  }

  One = 1

  OneNeutral (MkCustomInt a b) = MkCustomIntEq {
      eq = rewrite multZeroRightZero a
      in rewrite multZeroRightZero b
      in rewrite multOneRightNeutral a
      in rewrite multOneRightNeutral b
      in rewrite plusZeroRightNeutral a
      in Refl
    }
