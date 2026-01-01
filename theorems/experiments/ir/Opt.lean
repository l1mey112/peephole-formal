import theorems.iN
import theorems.experiments.ir.opt.M
import theorems.experiments.ir.opt.Reify
import theorems.experiments.ir.opt.Denote
import theorems.experiments.ir.opt.Rewrite
import theorems.experiments.ir.opt.Eval
import Lean
import Qq

open Lean Elab Meta
open Qq

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
  { impl := fun ir =>
    match ir with
      | IR.addNsw lhs rhs => IR.add lhs rhs
      | _ => ir

  , wf := by
      intros idx ξ σ lhs

      split <;> try rfl
      apply addNsw_refine_add
  }

elab "⟨⟨" ruleStx:term ":" exprStx:term "⟩⟩" : term => do
  let expr ← Term.withoutErrToSorry do Term.elabTerm exprStx none
  if expr.hasExprMVar then
    throwError m!"Type mismatch: The argument expression{indentD expr}\ncontains metavariables."

  have rule : Q(Rule) := ← Term.withoutErrToSorry do Term.elabTerm ruleStx q(Rule)
  if expr.hasExprMVar then
    throwError m!"Type mismatch: The argument expression{indentD expr}\ncontains metavariables."

  lambdaTelescope expr fun fvars body => do
    /- body : iN (ξ.get resultIdx) -/
    let (resultIdx, env) := ← MEnv.of fvars body; M.run' env do
      let reified ← reifyIRExpr resultIdx body
      let irProof ← reified.proof

      logInfo m!"one: {reified.irExpr}"

      let opt ← evalRule resultIdx reified.irExpr rule

      logInfo m!"two: {toExpr opt.ir'}"

      /- have ir'Q : Q(IR $resultIdx) := toExpr ir'

      /- ir' = rule.impl ir -/
      let proofType := q($ir'Q = @$(rule).impl $resultIdx $(reified.irExpr))

      /- then, as they're both inductive ASTs this can be proved by just running the code
        by doing Lean.reduceBool + Lean.ofReduceBool -/

      let rhs ← denoteIRExpr ir'
      let rhsProof ← rhs.proof

      check irProof
      check rhsProof

      logInfo m!"reifyProof: {← inferType irProof}"
      logInfo m!"denoteProof: {← inferType rhsProof}"

      let rwProof ← constructProof reified ir' rhs q(@($rule).wf)

      check rwProof
      logInfo m!"rwProof: {← inferType rwProof}" -/

    return expr

def f' := ⟨⟨addNsw_refine_add' : fun {n} (x : iN n) => x +nsw x⟩⟩
