
/-
 -/

structure PoisonOr (α : Type) where
  val : α
  poisonous : Bool
deriving Inhabited, DecidableEq

instance : Monad PoisonOr where
  pure x := ⟨x, false⟩
  bind x f :=
    let y := f x.val
    ⟨y.val, x.poisonous || y.poisonous⟩

abbrev iN (n : Nat) := PoisonOr (BitVec n)

def PoisonOr.poison [Inhabited α] : PoisonOr α :=
  ⟨default, true⟩

def PoisonOr.value (x : α) : PoisonOr α :=
  ⟨x, false⟩

namespace iN

def add? {n} (x y : BitVec n) : iN n :=
  .value (x + y)

def addNw {n} (x y : iN n)  : iN n := do
  let x' ← x
  let y' ← y
  if BitVec.saddOverflow x' y' then
    .poison
  else if BitVec.uaddOverflow x' y' then
    .poison
  else
    add? x' y'

end iN
