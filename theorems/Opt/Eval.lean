import theorems.Opt.Basic
import Lean
import Qq

open Lean Elab Meta
open Qq

unsafe def evalImplUnsafe (idx : Nat) (irExpr : Q(IR $idx)) (rule : Q(Rule)) : MetaM (IR idx) := do
  let expr := q(($rule).impl $irExpr)
  evalExpr (IR idx) q(IR $idx) expr

@[implemented_by evalImplUnsafe]
opaque evalImpl (idx : Nat) (irExpr : Q(IR $idx)) (rule : Q(Rule)) : MetaM (IR idx)

structure EvalRuleResult (idx : Nat) where
  ir' : IR idx
  irExpr' : Q(IR $idx)

  /--
  Proof that `ir' = rule.impl ir`
  -/
  proof : Expr


/--
Evaluate the rule. This uses the interpreter then the kernel to prove rfl.

The proof returned is always definitional equality.
-/
def evalRule (idx : Nat) (irExpr : Q(IR $idx)) (rule : Q(Rule)) : MetaM (EvalRuleResult idx) := do
  let ir' ← evalImpl idx irExpr rule

  have irExpr' : Q(IR $idx) := toExpr ir'
  have implEval : Q(IR $idx) := q(($rule).impl $irExpr)

  have : $implEval =Q $irExpr' := .unsafeIntro
  have proof : Q($implEval = $irExpr') := q(rfl)
  check proof

  return ⟨ir', irExpr', proof⟩


/-
TODO OLD

Evaluate the rule. This uses the interpreter then the kernel to prove rfl.

This could get slow, eventually I would want to trust the compiler and use
`Lean.ofReduceBool` so I can cut out the kernel and just use the interpreter.

Generally, you shouldn't assume that the proof returned is definitional equality,
as it very well could not be. (TODO check this)
-/
