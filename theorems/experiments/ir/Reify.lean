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
such that the entire expression is of type `iN (ξ.get result_idx)`. -/
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
  originalExpr : Expr

  /-- Proof that IR.eval ξ σ irExpr = originalExpr.  -/
  proof : M Expr

namespace ReifiedIR

def mkEvalIR (idx : Nat) (expr : Q(IR $idx)) : M Expr := do
  let st ← read
  return q(IR.eval $(st.ξQ) $(st.σQ) $expr)

end ReifiedIR

partial def reifyIRExpr (idx : Nat) (body : Expr) : M (ReifiedIR idx) := do
  let ⟨ξQ, σQ, σMap, _⟩ ← read
  have bodyQ : Q(iN <| ($ξQ).get $idx) := body

  match_expr body with
  | iN.poison _ =>

    let ir : IR idx := .poison
    have irExpr : Q(IR $idx) := toExpr ir

    have lhs : Q(iN <| ($ξQ).get $idx) := q(IR.eval $ξQ $σQ $irExpr)
    have : $lhs =Q $bodyQ := .unsafeIntro

    return ⟨ir, body, pure q(rfl : $lhs = $bodyQ)⟩

  | _ =>
    if let some fvarid := body.fvarId? then
      let some ⟨id, proof⟩ := σMap.get? fvarid
        | throwError "reifyIRExpr: unbound free variable {body}"

      return ⟨.var id, body, pure proof⟩

    throwError "reifyIRExpr: unsupported expression {body}"

elab "⟪" t:term "⟫" : term => do
  let t ← Term.elabTerm t none
  if t.hasExprMVar then
    throwError m!"expression contains metavariables:{indentD t}"

  lambdaTelescope t fun fvars body => do
    /- body : iN (ξ.get resultIdx) -/
    let (resultIdx, env) := ← ReifyEnv.of fvars body; M.run' env do
    let ir ← (reifyIRExpr resultIdx body).run env

    logInfo m!"ir: {repr ir.irExpr}"
    logInfo m!"proof: {← ir.proof}"

    check (← ir.proof)
    return toExpr ir.irExpr

--#eval ⟪fun {n} (x : iN n) => x +nsw x⟫
#eval ⟪fun {n} (x : iN n) => x⟫
