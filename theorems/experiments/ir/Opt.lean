import theorems.iN
import theorems.experiments.ir.opt.M
import theorems.experiments.ir.opt.Reify
import Lean

open Lean Elab Meta

/-

exports the `opt` tactic and `⟨⟨ ... ⟩⟩` for optimisation

-/

theorem addNsw_refine_add {n} (x y : iN n) : x +nsw y ~> x + y := by
  poison_unroll x y => a b

  by_cases h : a.saddOverflow b
  . rw [addNsw_saddOverflow_bitvec h]
    exact Rewrite.poison_rewrite (bitvec a + bitvec b)
  . rw [addNsw_not_saddOverflow_bitvec_eq_add h]
    simp [simp_iN]

def addNsw_refine_add' : Rule :=
  { valid := fun ξ => true
  , impl := fun ir => match ir with
      | IR.addNsw lhs rhs => IR.add lhs rhs
      | _ => ir

  , wf := by
      intros ξ _ σ _ lhs

      split <;> try rfl
      apply addNsw_refine_add
  }

#check funext

elab "⟨⟨" t:term "⟩⟩" : term => do
  let expr ← Term.withoutErrToSorry do Term.elabTerm t none
  if expr.hasExprMVar then
    throwError m!"Type mismatch: The argument expression{indentD expr}\ncontains metavariables."

  lambdaTelescope expr fun fvars body => do
    /- body : iN (ξ.get resultIdx) -/
    let (resultIdx, env) := ← MEnv.of fvars body; M.run' env do
    let ir ← (reifyIRExpr resultIdx body).run env

    logInfo m!"ir: {repr ir.irExpr}"
    logInfo m!"proof: {← ir.proof}"
    logInfo m!"proved: {← inferType (← ir.proof)}"

    let ir' := addNsw_refine_add'.impl ir.irExpr

    logInfo m!"ir': {repr ir'}"

    check (← ir.proof)
    return expr

def f' := ⟨⟨fun {n} (x : iN n) => x + x⟩⟩
