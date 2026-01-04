import Lean
import theorems.iN.iN_def
import theorems.iN.iN_rewrite

open Lean Meta Elab Parser Tactic

/-- Proves `f poison = poison`, for `f (poison : iN n) = (poison : iN n')`. -/
def proveCongruence (motive : Expr) (n n' : Expr) : MetaM Expr := do
  /- TODO make this function prove things nicely instead of unwrapping
    things down to the bone with simp which is slow and creates bloated
    proof terms -/

  let poison_app := mkApp motive $ mkApp (.const ``poison []) n
  let goalType ← mkEq poison_app $ mkApp (.const ``poison []) n'

  let proofMVar ← mkFreshExprMVar goalType .synthetic `h_cong_proof

  let ctx ← Simp.mkContext
    (config := { beta := true })
    (simpTheorems := #[← getSimpTheorems, ← simpIN.getTheorems])
    (congrTheorems := (← getSimpCongrTheorems))
  let (result?, _) ← simpGoal proofMVar.mvarId! ctx

  if let some _ := result? then
    /- throwTactic `orewrite x
      m!"unable to prove congruence goal `motive poison = poison` automatically with `simp [simp_iN]`" -/
    throwError m!"unable to prove congruence goal `motive poison = poison` automatically with `simp [simp_iN]`{indentD motive}"

  instantiateMVars proofMVar

def orewriteDo (mvarId : MVarId) (e : Expr)
    (heq : Expr) (symm : Bool) : MetaM MVarId := mvarId.withContext do

  mvarId.checkNotAssigned `orewrite
  let matchRewrite (e : Expr) (symm : Bool) : MetaM (Expr × Expr × Expr) := do
    match_expr e with
    | Rewrite n lhs rhs =>
      if symm then
        throwError m!"Invalid orewrite argument: Rewrite relation is not symmetric{indentExpr e}"

      return (n, lhs, rhs)
    | _ => throwError m!"Invalid orewrite argument: Expected an equality or rewrite, got type{indentExpr e}"

  let heqType ← instantiateMVars (← inferType heq)
  let (newMVars, _, heqType) ← forallMetaTelescopeReducing heqType
  /- `∀ (x y : iN 32), expr` into `expr`. -/
  let heq := mkAppN heq newMVars

  let occs : Occurrences := .all
  let e ← instantiateMVars e

  let (n', lhs, rhs) ← matchRewrite e symm
  let (n, x, y) ← match (← matchEq? heqType) with
    | some _ =>
      throwError m!"equality unsupported at the moment"
    | none => matchRewrite heqType symm

  -- h: x ~> y
  -- ⊢ lhs ~> rhs
  let lhsAbst ← kabstract lhs x occs
  unless lhsAbst.hasLooseBVars do
    throwTacticEx `orewrite mvarId m!"did not find instance of the pattern in the target expression{indentExpr lhs}\n"

  let α := (Expr.app (.const `iN []) n)
  let motive := Lean.mkLambda `_a BinderInfo.default α lhsAbst

  try
    check motive
  catch ex =>
    throwTacticEx `orewrite mvarId m!"motive is not type correct:{indentD motive}\nError: {ex.toMessageData}"

  /- Rewrite (_ : iN n) ~> (_ : iN n') -/
  let motiveProof ← liftMetaM $ proveCongruence motive n n'
  let congrProof ← mkAppM ``Rewrite.congrApp #[motive, motiveProof, heq]

  -- h : lhs ~> lhs'
  -- ⊢ lhs ~> rhs

  -- Rewrite.trans (lhs ~> lhs') (lhs' ~> rhs) (lhs ~> rhs)
  --                             ^^^^^^^^^^^^^ create a new metavariable/goal

  /- Construct final proof term with `Rewrite.trans` and a new goal. -/
  let unreducedLhsNew := mkApp motive y
  let newGoalType := mkAppN (.const ``Rewrite []) #[n', unreducedLhsNew, rhs]
  let newGoalMVar ← mkFreshExprMVar (some newGoalType)
  let fullProof ← mkAppM ``Rewrite.trans #[congrProof, newGoalMVar]
  mvarId.assign fullProof

  let newGoalId := newGoalMVar.mvarId!
  let (n_new, unreducedLhs, rhs_new) ← matchRewrite (← newGoalId.getType) false

  /- Beta reduce the annoying motive. -/
  let reducedLhs ← Core.betaReduce unreducedLhs
  let finalGoalType := mkAppN (.const ``Rewrite []) #[n_new, reducedLhs, rhs_new]
  let finalGoalId ← newGoalId.change finalGoalType

  return finalGoalId

/-
see the code for grewrite in Mathlib, the code for rewrite is hard to read and uses builtin stuff

TODO this is kinda terrible and won't handle multiple goals, oh well! ill probably fix this later
-/

/- orw [ ... ] at h -/
def optRewriteLocalDecl (stx : Syntax) (symm : Bool) (fvarId : FVarId) : TacticM Unit := withMainContext do
  _ := stx
  _ := symm
  _ := fvarId
  throwError m!"rewriting at the context not implemented yet"

/- orw [ ... ] at ⊢ -/
def optRewriteTarget (stx : Syntax) (symm : Bool) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  Term.withSynthesize <| goal.withContext do
    let heq ← elabTerm stx none true
    if heq.hasSyntheticSorry then
      throwAbortTactic

    let goal ← getMainGoal
    let e ← getMainTarget
    let e ← instantiateMVars e

    let r ← orewriteDo goal e heq symm
    replaceMainGoal [r]

/--
On a goal of `lhs ~> rhs`, apply a rewrite of the form `x ~> y`.
-/
syntax (name := optRewrite) "orewrite" rwRuleSeq (location)? : tactic

@[tactic optRewrite, inherit_doc optRewrite] def evalOptRewrite : Tactic := fun stx => do
  let loc := expandOptLocation stx[2]
  withRWRulesSeq stx[0] stx[1] fun symm term => do
    withLocation loc
      (optRewriteLocalDecl term symm ·)
      (optRewriteTarget term symm)
      (throwTacticEx `orewrite · "did not find instance of the pattern in the current goal")

/--
On a goal of `lhs ~> rhs`, apply a rewrite of the form `x ~> y`.
`orw` is like `orewrite` but also tries to close the goal with reducible `rfl`
and `apply Rewrite.poison_rewrite` to close goals of `poison ~> y`.
-/
macro (name := optRw) "orw " s:rwRuleSeq : tactic =>
  match s with
  | `(rwRuleSeq| [$rs,*]%$rbrak) =>
    -- We show the `rfl` state on `]`
    `(tactic| (orewrite [$rs,*]; with_annotate_state $rbrak (try rewrite_trivial)))
  | _ => Macro.throwUnsupported
