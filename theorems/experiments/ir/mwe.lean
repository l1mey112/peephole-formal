import Lean
import Qq
open Lean Elab Meta
open Qq

/--
LLVM-style integers with poison value.
-/
inductive iN (bits : Nat) : Type where
  | bitvec : BitVec bits → iN bits
  | poison : iN bits
deriving BEq

export iN (poison bitvec)

inductive IR : Nat → Type where
  | var (id : Nat) : IR idx
  | const_poison : IR idx

deriving BEq, Repr, Lean.ToExpr

structure PackediN where
  {n : Nat}
  x : iN n
deriving BEq

structure PackedIR where
  {idx : Nat}
  ir : IR idx
deriving Repr

def PackediN.truncate (pack : PackediN) (n : Nat) : iN n :=
  match pack.x with
  | poison => poison
  | bitvec a => bitvec (a.truncate n)

abbrev Assignment := Lean.RArray PackediN
abbrev WidthAssignment := Lean.RArray Nat

namespace IR

def eval (ξ : WidthAssignment) (σ : Assignment) : IR idx → iN (ξ.get idx)
  | var id =>
    let pack := σ.get id
    /- h is always true, this if is for totality -/
    if h : pack.n = (ξ.get idx) then
      h ▸ pack.x
    else
      pack.truncate (ξ.get idx)

  | const_poison => poison

end IR

structure ReifyEnv where
  /- "evals at assignments" -/
  ξQ : Q(WidthAssignment)
  σQ : Q(Assignment) /- varId → iN ?? -/

  /- FVarId → varId -/
  σMap : Std.HashMap FVarId Nat

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

  let σMap := Std.HashMap.ofArray assignment
  return ⟨ξQ, σQ, σMap⟩

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

  /- proof that IR.eval irExpr = originalExpr, or by rfl if none  -/
  proof : M (Option Expr)

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
    let ⟨ξQ, σQ, _⟩ ← read

    let proof := pure q(@reflect_poison_eval_poison $idx $ξQ $σQ)
    return ⟨IR.const_poison, body, proof⟩

  | _ =>
    let ⟨_, _, σMap⟩ ← read

    if let some fvarid := body.fvarId? then
      let some varId := σMap.get? fvarid
        | throwError "reifyIRExpr: unbound free variable {body}"

      return ⟨IR.var varId, body, pure none⟩

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

    if (← withTransparency (.all) <| isDefEq evalExpr body) then
      logInfo "yes"

    let expr ← mkEq evalExpr body
    logInfo m!"expr: {expr}"
    check expr

    if not (← isDefEq evalExpr body) then
      logInfo "expr is not definitionally equal"

    return toExpr ir.irExpr

/-
ir: IR.var 0
proof: <not-available>

expr: IR.eval (RArray.leaf n) (RArray.leaf { n := (RArray.leaf n).get 0, x := x }) (IR.var 0) = x
expr is not definitionally equal
-/
#eval ⟪fun {n} (x : iN n) => x⟫
