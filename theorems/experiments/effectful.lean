/- import theorems.iN.iN_def
import theorems.iN.iN_rewrite

def Ub (n : Nat) := Option (iN n)

inductive RewriteUB {n} : Ub n → Ub n → Prop where
  | ub : RewriteUB none none
  | rewrite : Rewrite a b → RewriteUB (some a) (some b) -/

#check Id
