symm : {left : Nat} -> {right : Nat} -> left = right -> right = left
symm prf = let
  in rewrite prf in Refl

plc_z : (n : Nat) -> n = n + 0
plc_z Z = Refl
plc_z (S k) = let
  rec = plc_z k
  in rewrite rec in Refl

plc_s : (k : Nat) -> (n : Nat) -> k + S n = S (k + n)
plc_s Z n = Refl
plc_s (S k) Z = let
  rec = plc_s k Z
  in rewrite rec in Refl
plc_s (S k) (S j) = let
  rec = plc_s k (S j)
  in rewrite rec in Refl

plc : (n : Nat) -> (m : Nat) -> n + m = m + n
plc Z m = plc_z m
plc (S k) m = let
  rec = plc k m
  in rewrite rec in symm $ plc_s m k
