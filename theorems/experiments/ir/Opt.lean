import theorems.iN
import theorems.experiments.ir.opt.M
import theorems.experiments.ir.opt.Reify
import theorems.experiments.ir.opt.Denote
import theorems.experiments.ir.opt.Rewrite
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
  { valid := fun ξ => true
  , impl := fun ir => match ir with
      | IR.addNsw lhs rhs => IR.add lhs rhs
      | _ => ir

  , wf := by
      intros idx ξ σ lhs

      split <;> try rfl
      apply addNsw_refine_add
  }

unsafe def evalImplUnsafe (idx : Nat) (irExpr : Q(IR $idx)) (rule : Q(Rule)) : MetaM (IR idx) := do
  let expr := q(($rule).impl $irExpr)
  evalExpr (IR idx) q(IR $idx) expr

@[implemented_by evalImplUnsafe]
opaque evalImpl (idx : Nat) (irExpr : Q(IR $idx)) (rule : Q(Rule)) : MetaM (IR idx)

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

      let ir' ← evalImpl resultIdx reified.irExpr rule

      let rhs ← denoteIRExpr ir'
      let rhsProof ← rhs.proof

      check irProof
      check rhsProof

      logInfo m!"reifyProof: {← inferType irProof}"
      logInfo m!"denoteProof: {← inferType rhsProof}"

      let rwProof ← constructProof reified ir' rhs q(@($rule).wf)

      check rwProof
      logInfo m!"rwProof: {← inferType rwProof}"

    return expr

def f' := ⟨⟨addNsw_refine_add' : fun {n} (x : iN n) => x +nsw x⟩⟩
