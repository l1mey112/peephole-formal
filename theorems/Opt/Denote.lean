import theorems.Opt.Basic
import theorems.Opt.M

import Lean
import Qq
open Lean Elab Meta
open Qq

/- TODO, eventually make this  -/
def M.IRtoExpr (ir : IR idx) : Expr := toExpr ir

structure DenotedIR (idx : Nat) where
  expr : Expr

  /--
  Essentially `toExpr ir`.
  Avoids quadratic behaviour from constantly computing toExpr on children.
  -/
  irExpr : Q(IR $idx)

  /-- Proof that IR.eval ξ σ originalIR = expr -/
  proof : M Expr

partial def denoteIRExpr {idx} (ir : IR idx) : M (DenotedIR idx) := do
  let ⟨ξQ, σQ, _, _, mapσ⟩ ← read

  /- insert defeq so typechecking plays nice -/
  have nQ : Q(Nat) := q(($ξQ).get $idx)
  have : $nQ =Q ($ξQ).get $idx := .unsafeIntro

  match ir with
  | .var id =>
    let ⟨fvar, proof⟩ := mapσ[id]!
    return ⟨mkFVar fvar, toExpr ir, pure proof⟩

  | .poison =>
    have lhs : Q(iN $nQ) := q(IR.eval $ξQ $σQ IR.poison)
    have bodyQ : Q(iN $nQ) := q(iN.poison)

    have : $lhs =Q $bodyQ := .unsafeIntro
    return ⟨bodyQ, toExpr ir, pure q(rfl : $lhs = $bodyQ)⟩

  | .const nv =>

    /- @OfNat.ofNat (BitVec n) 5 BitVec.instOfNat : BitVec n -/
    let nvQ : Q(Nat) := mkRawNatLit nv
    let ofNatEnc : Q(BitVec $nQ) := q(@OfNat.ofNat (BitVec (($ξQ).get $idx)) $nvQ BitVec.instOfNat)

    let irExpr : Q(IR $idx) := toExpr ir

    have lhs : Q(iN $nQ) := q(IR.eval $ξQ $σQ $irExpr)
    have bodyQ : Q(iN $nQ) := q(iN.bitvec $ofNatEnc)

    have : $lhs =Q $bodyQ := .unsafeIntro
    return ⟨bodyQ, irExpr, pure q(rfl : $lhs = $bodyQ)⟩

  | .add lhsIR rhsIR => denoteBinop lhsIR rhsIR ``IR.add ``HAdd.hAdd true ``add_congr
  | .addNsw lhsIR rhsIR => denoteBinop lhsIR rhsIR ``IR.addNsw ``iN.addNsw false ``addNsw_congr

  --| _ => throwError "unreachable"
where
  denoteBinop (lhsIR rhsIR : IR idx) (consName : Name) (instName : Name) (isHinst : Bool) (congrLemma : Name)
    : M (DenotedIR idx) := do

  let ⟨ξQ, σQ, _, _, _⟩ ← read

  /- insert defeq so typechecking plays nice -/
  have nQ : Q(Nat) := q(($ξQ).get $idx)
  have : $nQ =Q ($ξQ).get $idx := .unsafeIntro

  have idxQ : Q(Nat) := toExpr idx
  have congrLemmaQ := mkConst congrLemma
  have consQ := mkApp (mkConst consName) idxQ

  have instQ := ← if isHinst then
      mkAppOptM instName #[q(iN $nQ), q(iN $nQ), q(iN $nQ), none]
    else
      pure $ mkApp (mkConst instName) nQ

  let lhs ← denoteIRExpr lhsIR
  let rhs ← denoteIRExpr rhsIR

  have lhsExpr : Q(iN $nQ) := lhs.expr
  have rhsExpr : Q(iN $nQ) := rhs.expr

  /- lhsDenoted +nsw rhsDenoted -/
  let body : Q(iN $nQ) := mkApp2 instQ lhs.expr rhs.expr
  let irExpr : Q(IR $idx) := mkApp2 consQ lhs.irExpr rhs.irExpr

  let lhsEval ← M.mkEvalIR idx ξQ σQ lhs.irExpr
  let rhsEval ← M.mkEvalIR idx ξQ σQ rhs.irExpr

  have lhsProof : Q($lhsEval = $lhsExpr) := ← lhs.proof
  have rhsProof : Q($rhsEval = $rhsExpr) := ← rhs.proof

  /- body = IR.eval ξ σ lhs +nsw (IR.eval ξ σ rhs) =Q IR.eval ξ σ (IR.addNsw lhs rhs) -/
  /- these are definitionally equal, so it's fine anyway and IR.eval is on the outside -/
  let proof := mkApp7 congrLemmaQ nQ lhsExpr rhsExpr lhsEval rhsEval lhsProof rhsProof

  let actualType ← mkEq (← M.mkEvalIR idx ξQ σQ irExpr) body
  let proof := mkExpectedPropHint proof actualType

  return ⟨body, irExpr, pure proof⟩
