import theorems.experiments.ir.Basic
import theorems.experiments.ir.opt.Reflect

import Lean
import Qq
open Lean Elab Meta
open Qq

structure MEnv where
  /- "evals at assignments" -/
  ξQ : Q(WidthAssignment)
  σQ : Q(Assignment) /- varId → iN ?? -/

  /- FVarId → (varId, proof). index into σ and proof that IR.eval ξ σ (.var id) = x -/
  σMap : Std.HashMap FVarId <| Nat × Expr

  /- idx → FVarId -/
  mapξ : Array FVarId

  /- varId → (FVarId, proof) -/
  mapσ : Array (FVarId × Expr)

abbrev M := ReaderT MEnv MetaM

namespace M

def run' (env : MEnv) (m : M α) : MetaM α :=
  m.run env

def mkEvalIR (idx : Nat) (ξQ : Q(WidthAssignment)) (σQ : Q(Assignment)) (expr : Q(IR $idx)) : M Q(iN $ ($ξQ).get $idx) := do
  return q(IR.eval $ξQ $σQ $expr)

end M

def proveEval_var_eq (ξQ : Q(WidthAssignment)) (σQ : Q(Assignment)) (mapξ : Array FVarId)
    (id : Nat) (pair : FVarId × Nat) : MetaM (FVarId × (Nat × Expr)) := do

  let ⟨fvar, idx⟩ := pair

  have n : Q(Nat) := mkFVar $ mapξ[idx]!
  have x : Q(iN $n) := mkFVar fvar

  /- these are both definitional equalities, so we just need a bit of massaging -/

  have hb : Q((($σQ).get $id).n = $n) :=
    mkExpectedPropHint (← mkEqRefl n) q((($σQ).get $id).n = $n)

  have h : Q($hb ▸ (($σQ).get $id).x = $x) :=
    mkExpectedPropHint (← mkEqRefl x) q($hb ▸ (($σQ).get $id).x = $x)

  /- if Qq gives you issues, stop using q(·) and use Expr functions -/

  have : $n =Q ($ξQ).get $idx := .unsafeIntro
  have proof : Q(IR.eval $ξQ $σQ (IR.var $id) = $x) :=
    mkApp7 (mkConst ``IR.eval_var') (toExpr idx) (toExpr id) ξQ σQ x hb h

  return ⟨fvar, idx, proof⟩

def MEnv.of' (assignment : Array (FVarId × Nat)) (width_assignment : Array FVarId) : MetaM MEnv := do

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

  let assignments ← assignment.mapIdxM $ proveEval_var_eq ξQ' σQ' width_assignment

  let σMap := Std.HashMap.ofArray assignments
  let mapσ := assignments.map fun ⟨fvar, _, proof⟩ => ⟨fvar, proof⟩
  return ⟨ξQ', σQ', σMap, width_assignment, mapσ⟩

/--
Accepts expressions of the form
```lean
fun {n} ... {m} (x : iN n) ... (z : iN m) : iN n => ...
```
such that the entire expression is of type `iN (ξ.get result_idx)`.
-/
def MEnv.of (fvars : Array Expr) (body : Expr) : MetaM (Nat × MEnv) := do
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
    | _ => pure () /- throwError "reifyExpr: unsupported type" -/

  let body_type ← inferType body
  let resultIdx ← match_expr body_type with
  | iN nv =>

    let some assignmentIdx := width_assignment.findIdx? (fun widthFvar => widthFvar == nv.fvarId!)
      | throwError "reifyExpr: unbound, not previous free variable in Nat"

    pure assignmentIdx
  | _ => throwError "reifyExpr: unsupported body type {body_type}"

  let env ← MEnv.of' assignment width_assignment

  return ⟨resultIdx, env⟩
