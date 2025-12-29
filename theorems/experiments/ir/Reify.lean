import theorems.experiments.ir.Basic

import Lean
import Qq
open Lean Elab Meta
open Qq

structure ReifyEnv where
  /- "evals at assignments" -/
  ξQ : Q(WidthAssignment)
  σQ : Q(Assignment) /- varId → iN ?? -/

  /- FVarId → (varId, proof). index into σ and proof that IR.eval ξ σ (.var id) = x -/
  σMap : Std.HashMap FVarId <| Nat × Expr

  /- idx → FVarId -/
  mapξ : Std.HashMap Nat FVarId

def proveEval (ξQ : Q(WidthAssignment)) (σQ : Q(Assignment))
    (id : Nat) (pair : FVarId × Nat) : MetaM (FVarId × (Nat × Expr)) := do

  let ⟨fvar, idx⟩ := pair
  let irVar : IR idx := .var id

  let exprVar : Q(iN <| ($ξQ).get $idx) := mkFVar fvar

  let irVarExpr : Q(IR $idx) := toExpr irVar
  let proofType : Q(Prop) := q(IR.eval $ξQ $σQ $irVarExpr = $exprVar)

  /- this cannot be proved definitionally! we need to use simp unfortunately.. -/
  let proofMVar ← mkFreshExprMVar proofType .synthetic `proveEval

  let mut simpThms ← getSimpTheorems
  simpThms ← simpThms.addDeclToUnfold ``IR.eval

  /- TODO this is unacceptably huge as a proof term, use the theorem/lemma you created before
    as the hypotheses are definitionally true and only requires dumping the ξ around -/

  let ctx ← Simp.mkContext
    (config := { beta := true })
    (simpTheorems := #[← getSimpTheorems, simpThms])
    (congrTheorems := (← getSimpCongrTheorems))

  let (result?, _) ← simpGoal proofMVar.mvarId! ctx

  if let some _ := result? then
    throwError m!"unable to prove goal {proofType} (unreachable)"

  return ⟨fvar, idx, ← instantiateMVars proofMVar⟩

def ReifyEnv.of' (assignment : Array (FVarId × Nat)) (width_assignment : Array FVarId) : MetaM ReifyEnv := do

  let mut ξQ' : Q(WidthAssignment) := q(.leaf default)
  let mut σQ' : Q(Assignment) := q(.leaf default)

  if h : 0 < width_assignment.size then
    let width_assignment' : RArray FVarId :=
      RArray.ofArray width_assignment h

    have ξQ : Q(WidthAssignment) := ← width_assignment'.toExpr q(Nat) fun (fvar : FVarId) => mkFVarEx fvar

    if h' : 0 < assignment.size then
      let assignment' : RArray (FVarId × Nat) :=
        RArray.ofArray assignment h'

      have σQ : Q(Assignment) := ← assignment'.toExpr q(PackediN) fun (⟨x, idx⟩ : FVarId × Nat) =>
        /- we want iN (ξ.get idx) -/
        /- ⟨ξ.get idx, x⟩ -/

        have idxQ : Q(Nat) := toExpr idx
        have xQ : Q(iN (($ξQ).get $idxQ)) := mkFVarEx x
        have fid : Q(PackediN) := q(@PackediN.mk (($ξQ).get $idxQ) $xQ)
        fid

      σQ' := σQ
    ξQ' := ξQ

  let mapξ := Std.HashMap.ofArray $ width_assignment.mapIdx (·, ·)
  let σMap := Std.HashMap.ofArray (← assignment.mapIdxM $ proveEval ξQ' σQ')
  return ⟨ξQ', σQ', σMap, mapξ⟩

/--
Accepts expressions of the form
```lean
fun {n} ... {m} (x : iN n) ... (z : iN m) : iN n => ...
```
such that the entire expression is of type `iN (ξ.get result_idx)`.
--/
def ReifyEnv.of (fvars : Array Expr) (body : Expr) : MetaM (Nat × ReifyEnv) := do
  /- map each type iN n -> idx of WidthAssignment -/
  /- these are fvars being m, n, ... -/
  let mut width_assignment : Array FVarId := #[]

  /- map each expr x -> idx of Assignment -/
  let mut assignment : Array (FVarId × Nat) := #[]

  for fvar in fvars do
    /- https://github.com/leanprover-community/quote4/issues/36 -/
    let fvar_type ← inferType fvar

    match_expr fvar_type with
    | Nat =>
      width_assignment := width_assignment.push fvar.fvarId!
    | iN nv =>

      /- n should be an fvar, if we have for example (x : iN 32),
        we should encode it as ∀n : Nat, n = 32 → ... inside valid.
        this is unhandled for now -/
      let some assignmentIdx := width_assignment.findIdx? (fun widthFvar => widthFvar == nv.fvarId!)
        | throwError "reifyExpr: unbound, not previous free variable in Nat"

      assignment := assignment.push (fvar.fvarId!, assignmentIdx)
    | _ => throwError "reifyExpr: unsupported type"

  let body_type ← inferType body
  let resultIdx ← match_expr body_type with
  | iN nv =>

    let some assignmentIdx := width_assignment.findIdx? (fun widthFvar => widthFvar == nv.fvarId!)
      | throwError "reifyExpr: unbound, not previous free variable in Nat"

    pure assignmentIdx
  | _ => throwError "reifyExpr: unsupported body type {body_type}"

  let env ← ReifyEnv.of' assignment width_assignment

  return ⟨resultIdx, env⟩

abbrev M := ReaderT ReifyEnv MetaM

namespace M

def run' (env : ReifyEnv) (m : M α) : MetaM α :=
  m.run env

end M


structure ReifiedIR (idx : Nat) where
  irExpr : IR idx
  expr : Q(IR $idx) /- toExpr irExpr -/

  originalExpr : Expr

  /-- Proof that IR.eval ξ σ irExpr = originalExpr.  -/
  proof : M Expr

namespace ReifiedIR

def mkEvalIR (idx : Nat) (ξQ : Q(WidthAssignment)) (σQ : Q(Assignment)) (expr : Q(IR $idx)) : M Q(iN $ ($ξQ).get $idx) := do
  return q(IR.eval $ξQ $σQ $expr)

end ReifiedIR


theorem addNsw_congr (n : Nat) (lhs rhs lhs' rhs' : iN n) (h1 : lhs' = lhs) (h2 : rhs' = rhs)
    : lhs' +nsw rhs' = lhs +nsw rhs := by simp_all

/- IR.eval ξ σ (IR.var 0) +nsw IR.eval ξ σ (IR.var 0) = x +nsw x -/

theorem eval_addNsw_abstract {idx} (ξ : WidthAssignment) (σ : Assignment) (lhs rhs : IR idx)
    : IR.eval ξ σ lhs +nsw (IR.eval ξ σ rhs) = IR.eval ξ σ (IR.addNsw lhs rhs) := rfl

partial def reifyIRExpr (idx : Nat) (body : Expr) : M (ReifiedIR idx) := do
  let ⟨ξQ, σQ, σMap, _⟩ ← read

  /- insert defeq so typechecking plays nice -/
  have nQ : Q(Nat) := q(($ξQ).get $idx)
  have : $nQ =Q ($ξQ).get $idx := .unsafeIntro

  have bodyQ : Q(iN $nQ) := body

  match_expr body with
  | iN.poison _ =>

    let ir : IR idx := .poison
    have irExpr : Q(IR $idx) := toExpr ir

    have lhs : Q(iN $nQ) := q(IR.eval $ξQ $σQ $irExpr)
    have : $lhs =Q $bodyQ := .unsafeIntro

    return ⟨ir, toExpr ir, body, pure q(rfl : $lhs = $bodyQ)⟩

  | iN.addNsw _ lhsExpr rhsExpr =>
    have lhsExpr : Q(iN $nQ) := lhsExpr
    have rhsExpr : Q(iN $nQ) := rhsExpr

    let lhs ← reifyIRExpr idx lhsExpr
    let rhs ← reifyIRExpr idx rhsExpr

    let ir : IR idx := .addNsw lhs.irExpr rhs.irExpr
    let irExpr : Q(IR $idx) := q(IR.addNsw $(lhs.expr) $(rhs.expr))

    let lhsEval ← ReifiedIR.mkEvalIR idx ξQ σQ lhs.expr
    let rhsEval ← ReifiedIR.mkEvalIR idx ξQ σQ rhs.expr

    have lhsProof : Q($lhsEval = $lhsExpr) := ← lhs.proof
    have rhsProof : Q($rhsEval = $rhsExpr) := ← rhs.proof

    /- body = IR.eval ξ σ lhs +nsw (IR.eval ξ σ rhs) =Q IR.eval ξ σ (IR.addNsw lhs rhs) -/
    /- these are definitionally equal, so it's fine anyway and IR.eval is on the outside -/
    let proof := q(addNsw_congr $nQ $lhsExpr $rhsExpr $lhsEval $rhsEval $lhsProof $rhsProof)

    return ⟨ir, irExpr, body, pure proof⟩

  | _ =>
    if let some fvarid := body.fvarId? then
      let some ⟨id, proof⟩ := σMap.get? fvarid
        | throwError "reifyIRExpr: unbound free variable {body}"

      let ir : IR idx := .var id
      return ⟨ir, toExpr ir, body, pure proof⟩

    throwError "reifyIRExpr: unsupported expression {body}"

elab "⟪" t:term "⟫" : term => do
  let expr ← Term.withoutErrToSorry do Term.elabTerm t none
  if expr.hasExprMVar then
    throwError m!"Type mismatch: The argument expression{indentD expr}\ncontains metavariables."

  lambdaTelescope expr fun fvars body => do
    /- body : iN (ξ.get resultIdx) -/
    let (resultIdx, env) := ← ReifyEnv.of fvars body; M.run' env do
    let ir ← (reifyIRExpr resultIdx body).run env

    logInfo m!"ir: {repr ir.irExpr}"
    logInfo m!"proof: {← ir.proof}"
    logInfo m!"proved: {← inferType (← ir.proof)}"

    check (← ir.proof)
    return toExpr ir.irExpr

#eval ⟪fun {n} (x : iN n) => x +nsw x +nsw x +nsw x +nsw x⟫
--#eval ⟪fun {n} (x : iN n) => x⟫
