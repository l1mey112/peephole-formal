import theorems.experiments.ir.Basic

import Lean
import Qq
open Lean Elab Meta
open Qq

/-- Some assignment `x : iN n`. -/
structure FVarAssignment where
  /-- Index into σ. -/
  id : Nat

  /-- Proof that `(σ.get id).n = n`. -/
  hb : Expr
  /-- Proof that `hb ▸ (σ.get id).x = x`. -/
  h : Expr

def FVarAssignment.ofPair (mapξ : Std.HashMap Nat FVarId) (σQ : Q(Assignment))
    (id : Nat) (pair : FVarId × Nat) : MetaM (FVarId × FVarAssignment) := do

  let ⟨fvar, idx⟩ := pair
  have n : Q(Nat) := mkFVar $ mapξ.get! idx
  have x : Q(iN $n) := mkFVar fvar

  have hb : Q((($σQ).get $id).n = $n) :=
    mkExpectedPropHint (← mkEqRefl n) q((($σQ).get $id).n = $n)

  have h : Q($hb ▸ (($σQ).get $id).x = $x) :=
    mkExpectedPropHint (← mkEqRefl x) q($hb ▸ (($σQ).get $id).x = $x)

  let assignment : FVarAssignment := ⟨id, hb, h⟩
  return ⟨fvar, assignment⟩

structure ReifyEnv where
  /- "evals at assignments" -/
  ξQ : Q(WidthAssignment)
  σQ : Q(Assignment) /- varId → iN ?? -/

  /- FVarId → varId -/
  σMap : Std.HashMap FVarId FVarAssignment

  /- idx → FVarId -/
  mapξ : Std.HashMap Nat FVarId

def ReifyEnv.of' (assignment : Array (FVarId × Nat)) (width_assignment : Array FVarId)
  (h : 0 < assignment.size) (h' : 0 < width_assignment.size) : MetaM ReifyEnv := do
  let assignment' : RArray (FVarId × Nat) :=
    RArray.ofArray assignment h

  let width_assignment' : RArray FVarId :=
    RArray.ofArray width_assignment h'

  have ξQ : Q(WidthAssignment) :=
    ← width_assignment'.toExpr q(Nat) fun (fvar : FVarId) => mkFVarEx fvar

  have σQ : Q(Assignment) :=
    ← assignment'.toExpr q(PackediN) fun (⟨x, idx⟩ : FVarId × Nat) =>
      /- we want iN (ξ.get idx) -/
      /- ⟨ξ.get idx, x⟩ -/

      have idxQ : Q(Nat) := toExpr idx

      have xQ : Q(iN (($ξQ).get $idxQ)) := mkFVarEx x
      have fid : Q(PackediN) := q(@PackediN.mk (($ξQ).get $idxQ) $xQ)
      fid

  let mapξ := Std.HashMap.ofArray $ width_assignment.mapIdx (·, ·)
  let fvarAssignments ←
    assignment.mapIdxM $ FVarAssignment.ofPair mapξ σQ

  let σMap := Std.HashMap.ofArray fvarAssignments
  return ⟨ξQ, σQ, σMap, mapξ⟩

/- accepts expressions of the form
  `fun {n} ... {m} (x : iN n) ... (z : iN m) : iN n => ...` -/
/- entire expression is iN (ξ.get result_idx) -/
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

  if h : ¬0 < assignment.size then
    unreachable!
  else if h' : ¬0 < width_assignment.size then
    unreachable!
  else

  let body_type ← inferType body
  let resultIdx ← match_expr body_type with
  | iN nv =>

    let some assignmentIdx := width_assignment.findIdx? (fun widthFvar => widthFvar == nv.fvarId!)
      | throwError "reifyExpr: unbound, not previous free variable in Nat"

    pure assignmentIdx
  | _ => throwError "reifyExpr: unsupported body type {body_type}"

  let env ← ReifyEnv.of' assignment width_assignment
    (by exact Decidable.of_not_not h) (by exact Decidable.of_not_not h')

  return ⟨resultIdx, env⟩

abbrev M := ReaderT ReifyEnv MetaM

namespace M

def run' (env : ReifyEnv) (m : M α) : MetaM α :=
  m.run env

end M


structure ReifiedIR (idx : Nat) where
  irExpr : IR idx
  originalExpr : Expr

  /-- Proof that IR.eval irExpr = originalExpr.  -/
  /- TODO add Option for none if holds by rfl -/
  proof : M Expr

namespace ReifiedIR

def mkEvalIR (idx : Nat) (expr : Q(IR $idx)) : M Expr := do
  let st ← read
  return q(IR.eval $(st.ξQ) $(st.σQ) $expr)

end ReifiedIR

theorem reflect_poison_eval_poison {idx ξ σ}
  : IR.eval ξ σ (IR.const_poison : IR idx) = (poison : iN (ξ.get idx)) := rfl

partial def reifyIRExpr (idx : Nat) (body : Expr) : M (ReifiedIR idx) := do
  match_expr body with
  | iN.poison _ =>
    let ⟨ξQ, σQ, _, _⟩ ← read

    /- TODO this holds definitionally, so no need to prove this anyway -/
    let proof := pure q(@reflect_poison_eval_poison $idx $ξQ $σQ)
    return ⟨IR.const_poison, body, proof⟩

  | _ =>
    let ⟨ξQ, _, σMap, mapξ⟩ ← read

    if let some fvarid := body.fvarId? then
      let some ⟨id, _, _⟩ := σMap.get? fvarid
        | throwError "reifyIRExpr: unbound free variable {body}"

      /- TODO proof -/
      /- TODO prove symbolically by `simp [IR.eval]` -/
      return ⟨IR.var id, body, pure $ mkFVar fvarid⟩

    throwError "reifyIRExpr: unsupported expression {body}"

elab "⟪" t:term "⟫" : term => do
  let t ← Term.elabTerm t none
  lambdaTelescope t fun fvars body => do
    /- body : iN (ξ.get resultIdx) -/
    let (resultIdx, env) := ← ReifyEnv.of fvars body; M.run' env do


    let ir ← (reifyIRExpr resultIdx body).run env

    logInfo m!"ir: {repr ir.irExpr}"
    logInfo m!"proof: {← ir.proof}"

    have irExpr : Q(IR $resultIdx) := toExpr ir.irExpr
    let evalExpr : Expr ← ReifiedIR.mkEvalIR resultIdx irExpr
    /- IR.eval ... =  -/

    /- logInfo m!"print: {← isDefEq evalExpr}"
 -/

    if (← withTransparency (.all) <| isDefEq evalExpr body) then
      logInfo "yes"

    /- if not (← isDefEq evalExpr body) then
      logInfo "why?" -/

    let expr ← mkEq evalExpr body
    logInfo m!"expr: {expr}"
    check expr

    return t

--#eval ⟪fun {n} (x : iN n) => x +nsw x⟫
#eval ⟪fun {n} (x : iN n) => x⟫
