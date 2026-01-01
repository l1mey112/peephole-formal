import theorems.iN
import theorems.experiments.ir.opt.M
import theorems.experiments.ir.opt.Reify
import theorems.experiments.ir.opt.Denote
import theorems.experiments.ir.opt.Eval
import Lean
import Qq

open Lean Elab Meta Tactic
open Qq

/-

exports the `opt` tactic and `⟦ opt : func ⟧` for optimisation

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

theorem chainOpt_proof {idx} (ξ) (σ) (ir ir' : IR idx) (lhs rhs : iN (ξ.get idx))
    (lhsProof : IR.eval ξ σ ir = lhs)
    (rhsProof : IR.eval ξ σ ir' = rhs)
    (wf : IR.eval ξ σ ir ~> IR.eval ξ σ ir')
    : lhs ~> rhs  := by

  rw [← lhsProof, ← rhsProof]
  exact wf

def chainOpt {idx}
    (reified : ReifiedIR idx) (rule : Q(Rule)) (opt : EvalRuleResult idx) (denoted : DenotedIR idx)
    : M Expr := do

  let ⟨ξQ, σQ, _, _, _⟩ ← read

  let lhsProof ← reified.proof
  let wf := q(@$(rule).wf $idx $ξQ $σQ $(reified.irExpr))
  let rhsProof ← denoted.proof

  /- opt.proof is ignored because at the moment it is definitional equality -/
  _ := opt

  mkAppM ``chainOpt_proof
    #[ξQ, σQ, reified.irExpr, denoted.irExpr, reified.originalExpr, denoted.expr, lhsProof, rhsProof, wf]


private def elabConstName (stx : TSyntax `ident) (expected : Option Q(Type)) : TermElabM Expr := do
  /- we're basically "elaborating" `stx` as `@stx` -/
  let expr := mkConst stx.getId
  Term.ensureHasType expected expr


elab "⟦" ruleStx:ident ":" exprStx:ident "⟧" : term => do
  let expr' ← elabConstName exprStx none
  let expr := (← unfoldDefinition? expr').getD expr'
  have rule : Q(Rule) := ← elabConstName ruleStx (some q(Rule))

  if not expr.isLambda then
    throwError m!"Expected lambda in expression{indentD expr}"

  lambdaTelescope expr fun fvars body => do
    /- body : iN (ξ.get resultIdx) -/
    let (resultIdx, env) := ← MEnv.of fvars body;

    M.run' env do
      let reified ← reifyIRExpr resultIdx body
      let opt ← evalRule resultIdx reified.irExpr rule
      let denoted ← denoteIRExpr opt.ir'

      /- let p ← chainOpt reified rule opt denoted
      check p -/
      mkLambdaFVars fvars denoted.expr

/--
Given the goal
```
⊢ lhs ~> rhs
```
this tactic optimises `lhs ~> lhs'` and transforms the goal into
```
⊢ lhs' ~> rhs
```
-/
elab "opt0" : tactic => withMainContext do
  let mvarId ← getMainGoal
  mvarId.checkNotAssigned `opt


  let e ← getMainTarget
  let e ← instantiateMVars e

  /- the aim is to revert the entire theorem statement
    until it's just a ∀ with a heap of bvars

    then, just go ahead and do forallTelescope -/
  /-
    ⊢ ∀ {n : Nat} (x : iN n), x +nsw x ~> x + x

    into
      f := fun {n : Nat} (x : iN n) => x +nsw x

    =>
      f' := fun {n : Nat} (x : iN n) => x + x

    then deduce
      ⊢ f x ~> f' x

    and hence do transitive chaining
  -/


  /- let (_, lhs, rhs) ← match_expr e with
  | Rewrite n lhs rhs => pure (n, lhs, rhs)
  | _ => throwTacticEx `opt mvarId m!"Not a rewrite{indentExpr e}"
  -/

  sorry

macro "opt " : tactic =>
  `(tactic| (opt0; try (with_reducible rfl)))

def f {n} (x : iN n) := x +nsw x
def f' := ⟦addNsw_refine_add' : f⟧

theorem f_opt_f' {n} (x : iN n) : f x ~> f' x := by
  unfold f f'
  revert n
  opt0
