module Setoid

%access public export

infix 5 :=:
interface Setoid Carrier where
  (:=:) : (a, b : Carrier) -> Type
  Reflx : (a : Carrier) -> a :=: a
  Sym : (a, b : Carrier) -> a :=: b -> b :=: a
  Trans : (a, b, c : Carrier) -> a :=: b -> b :=: c -> a :=: c


interface (Setoid Carrier, Num Carrier, Neg Carrier) => Ring Carrier where
  PlusComm : (a, b : Carrier) -> (a + b :=: b + a)
  PlusAssoc : (a, b, c : Carrier) -> a + (b + c) :=: a + b + c
  Zero : Carrier
  ZeroNeutral : (a : Carrier) -> a + Zero :=: a
  NegateEx : (a : Carrier) -> a + (negate a) :=: Zero
  MultComm : (a, b : Carrier) -> (a * b :=: b * a)
  MultAssoc : (a, b, c : Carrier) -> a * (b * c) :=: a * b * c
  MultDistrLeft : (a, b, c : Carrier) -> a * (b + c) :=: (a * b) + (a * c)
  MultDistrRight : (a, b, c : Carrier) -> (a + b) * c :=: (a * c) + (b * c)
  One : Carrier
  OneNeutral : (a : Carrier) -> a * One :=: a
