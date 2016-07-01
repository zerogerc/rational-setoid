module Setoid

%access public export

-- R рефлексивно, если для любого (x : A) мы можем создать (R x x)
Reflx : {A : Type} -> (R : A -> A -> Type) -> Type
Reflx {A} R = (x : A) -> R x x

-- R симметрично, если из (R x y) мы можем создать (R y x)
Sym : {A : Type} -> (R : A -> A -> Type) -> Type
Sym {A} R = (x : A) -> (y : A) -> R x y -> R y x

-- R транзитивно, если из (R x y) и (R y z) мы можем создать (R x z)
Trans : {A : Type} -> (R : A -> A -> Type) -> Type
Trans {A} R = (x : A) -> (y : A) -> (z : A) -> R x y -> R y z -> R x z

-- Отношение эквивалентности -- это рефлексивное, симметричное и транзитивное отношение
data IsEquivalence : {A : Type} -> (R : A -> A -> Type) -> Type where
    EqProof : {A : Type} -> (R : A -> A -> Type) -> Reflx {A} R -> Sym {A} R -> Trans {A} R -> IsEquivalence {A} R

-- Сетоид -- это множество с заданым на ним отношением эквивалентности
record Setoid where
    constructor MkSetoid
    Carrier : Type
    Equiv : Carrier -> Carrier -> Type
    EquivProof : IsEquivalence Equiv
