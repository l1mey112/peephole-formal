import theorems.iN
import theorems.experiments.ir.opt.M
import theorems.experiments.ir.opt.Reify
import theorems.experiments.ir.opt.Denote
import Lean

open Lean Elab Meta


/-
ir  = reify lhs     (IR.eval ir = lhs)
ir' = opt ir        (IR.eval ir ~> IR.eval ir')   (opt.wf)
rhs = denote ir'    (IR.eval ir' = rhs)
-/

/- ir, ir' = impl ir (no proof of this) -/

/-

theorem : ir' = impl ir := by decide

-/

def constructProof {idx : Nat} (lhs : ReifiedIR idx) (ir' : IR idx) (rhs : DenotedIR idx)
    (wfExpr : Expr) /- Q(∀ idx ξ σ lhs, lhs.ir ~> ir' ) -/
    : M Expr := do

  let ⟨ξQ, σQ, _, _, _⟩ ← read

  let wfExpr' := mkApp3 wfExpr ξQ σQ lhs.irExpr


  sorry
