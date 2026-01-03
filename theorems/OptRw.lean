import Lean
import theorems.iN.iN_def
import theorems.iN.iN_rewrite

open Lean Elab Tactic Meta

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
    /- throwTactic `opt_rewrite x
      m!"unable to prove congruence goal `motive poison = poison` automatically with `simp [simp_iN]`" -/
    throwError m!"unable to prove congruence goal `motive poison = poison` automatically with `simp [simp_iN]`{indentD motive}"

  instantiateMVars proofMVar

/--
On a goal of `lhs ~> rhs`, apply a rewrite of the form `x ~> y`.
-/
syntax (name := optRewrite) "opt_rewrite" term : tactic

/--
On a goal of `lhs ~> rhs`, apply a rewrite of the form `x ~> y`.
`opt_rw` is like `opt_rewrite` but also tries to close the goal with reducible `rfl`
and `apply Rewrite.poison_rewrite` to close goals of `poison ~> y`.
-/
syntax (name := optRw) "opt_rw" term : tactic

elab "opt_rewrite" t:term : tactic => withMainContext do
  let mvarId ← getMainGoal
  mvarId.checkNotAssigned `opt_rewrite

  let matchRewrite (e : Expr) : MetaM (Expr × Expr × Expr) := do
    match_expr e with
    | Rewrite n lhs rhs => return (n, lhs, rhs)
    | _ => throwTacticEx `opt_rewrite mvarId m!"not a rewrite{indentExpr e}"

  let heq ← Term.withoutErrToSorry do
    elabTerm t none true
  if heq.hasSyntheticSorry then
    throwAbortTactic

  let heqType ← instantiateMVars (← inferType heq)
  let (newMVars, _, heqType) ← forallMetaTelescopeReducing heqType
  /- `∀ (x y : iN 32), expr` into `expr`. -/
  let heq := mkAppN heq newMVars

  let occs : Occurrences := .all
  let e ← getMainTarget
  let e ← instantiateMVars e

  let (n', lhs, rhs) ← matchRewrite e
  let (n, x, y) ← matchRewrite heqType

  -- h: x ~> y
  -- ⊢ lhs ~> rhs
  let lhsAbst ← kabstract lhs x occs
  unless lhsAbst.hasLooseBVars do
    throwTacticEx `opt_rewrite mvarId m!"did not find instance of the pattern in the target expression{indentExpr lhs}\n"

  let α := (Expr.app (.const `iN []) n)
  let motive := Lean.mkLambda `_a BinderInfo.default α lhsAbst

  try
    check motive
  catch ex =>
    throwTacticEx `opt_rewrite mvarId m!"motive is not type correct:{indentD motive}\nError: {ex.toMessageData}"

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
  let (n_new, unreducedLhs, rhs_new) ← matchRewrite (← newGoalId.getType)

  /- Beta reduce the annoying motive. -/
  let reducedLhs ← Core.betaReduce unreducedLhs
  let finalGoalType := mkAppN (.const ``Rewrite []) #[n_new, reducedLhs, rhs_new]
  let finalGoalId ← newGoalId.change finalGoalType

  replaceMainGoal [finalGoalId]

/- TODO when the identifier doesn't exist, nothing happens. fix this -/

macro "opt_rw " t:term : tactic =>
  `(tactic| (opt_rewrite $t; try rewite_trivial))
