import theorems.iN

inductive IR : Nat → Type where
  | var (id : Nat) : IR idx
  | const (val : Nat) : IR idx
  | poison : IR idx

  | add (lhs rhs : IR idx) : IR idx
  | addNsw (lhs rhs : IR idx) : IR idx
deriving BEq, Repr, Lean.ToExpr

deriving instance BEq for iN

structure PackediN where
  {n : Nat}
  x : iN n
deriving BEq, Inhabited

structure PackedIR where
  {idx : Nat}
  ir : IR idx
deriving Repr

def PackediN.truncate (pack : PackediN) (n : Nat) : iN n :=
  match pack.x with
  | poison => poison
  | bitvec a => a.truncate n

abbrev Assignment := Lean.RArray PackediN
abbrev WidthAssignment := Lean.RArray Nat

namespace IR

def eval (ξ : WidthAssignment) (σ : Assignment) : IR idx → iN (ξ.get idx)
  | .var id =>
    let pack := σ.get id
    /- h is always true, this if is for totality.

      unlike `bv_decide`, we lose out on definitional equality for `.var` so the
      goal needs to be proven symbolically by `simp [IR.eval]` -/
    if h : pack.n = (ξ.get idx) then
      h ▸ pack.x
    else
      pack.truncate (ξ.get idx)

  | .const val => iN.bitvec val
  | .poison => iN.poison

  | .add lhs rhs => (eval ξ σ lhs) + (eval ξ σ rhs)
  | .addNsw lhs rhs => (eval ξ σ lhs) +nsw (eval ξ σ rhs)

  /- | add lhs rhs => iN.add (eval σ lhs) (eval σ rhs)
  | addNsw lhs rhs => iN.addNsw (eval σ lhs) (eval σ rhs)
  | addNuw lhs rhs => iN.addNuw (eval σ lhs) (eval σ rhs)
  | addNw lhs rhs => iN.addNw (eval σ lhs) (eval σ rhs) -/

end IR


/--
For the implementation to optimise, it needs to know whether or not the width assignment respect the `valid` prop.
-/
structure Rule where
  --valid : WidthAssignment → Bool

  impl : {idx : Nat} → IR idx → IR idx

  /- TODO implement proper hypothesis handling
    we have constraints for iN, but no constraints for bitwidths -/
  wf : ∀ {idx} (ξ : WidthAssignment) /- (ξvalid : valid ξ) -/ (σ : Assignment) (lhs : IR idx),
    (IR.eval ξ σ lhs) ~> (IR.eval ξ σ (impl lhs))
