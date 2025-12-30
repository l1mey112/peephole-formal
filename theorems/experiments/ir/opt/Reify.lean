import theorems.experiments.ir.Basic
import theorems.experiments.ir.opt.M

import Lean
import Qq
open Lean Elab Meta
open Qq

structure ReifiedIR (idx : Nat) where
  irExpr : IR idx
  expr : Q(IR $idx) /- toExpr irExpr -/

  originalExpr : Expr

  /-- Proof that IR.eval ξ σ irExpr = originalExpr.  -/
  proof : M Expr

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

  | iN.addNsw _ lhsExpr rhsExpr => reifyBinop idx lhsExpr rhsExpr IR.addNsw ``IR.addNsw ``addNsw_congr
  | iN.add _ lhsExpr rhsExpr => reifyBinop idx lhsExpr rhsExpr IR.addNsw ``IR.add ``add_congr

  | _ =>
    if let some fvarid := body.fvarId? then
      let some ⟨id, proof⟩ := σMap.get? fvarid
        | throwError "reifyIRExpr: unbound free variable {body}"

      let ir : IR idx := .var id
      return ⟨ir, toExpr ir, body, pure proof⟩

    throwError "reifyIRExpr: unsupported expression {body}"
where
  reifyBinop (idx : Nat) (lhsExpr rhsExpr : Expr) (cons : IR idx → IR idx → IR idx)
      (consName : Name) (congrLemma : Name)
      : M (ReifiedIR idx) := do

    let ⟨ξQ, σQ, _, _⟩ ← read

    /- insert defeq so typechecking plays nice -/
    have nQ : Q(Nat) := q(($ξQ).get $idx)
    have : $nQ =Q ($ξQ).get $idx := .unsafeIntro

    have idxQ : Q(Nat) := toExpr idx
    have congrLemmaQ := mkConst congrLemma
    have consQ : Q(IR $idx → IR $idx → IR $idx) := mkApp (mkConst consName) idxQ

    have lhsExpr : Q(iN $nQ) := lhsExpr
    have rhsExpr : Q(iN $nQ) := rhsExpr

    let lhs ← reifyIRExpr idx lhsExpr
    let rhs ← reifyIRExpr idx rhsExpr

    let ir : IR idx := cons lhs.irExpr rhs.irExpr
    let irExpr : Q(IR $idx) := q($consQ $(lhs.expr) $(rhs.expr))

    let lhsEval ← M.mkEvalIR idx ξQ σQ lhs.expr
    let rhsEval ← M.mkEvalIR idx ξQ σQ rhs.expr

    have lhsProof : Q($lhsEval = $lhsExpr) := ← lhs.proof
    have rhsProof : Q($rhsEval = $rhsExpr) := ← rhs.proof

    /- body = IR.eval ξ σ lhs +nsw (IR.eval ξ σ rhs) =Q IR.eval ξ σ (IR.addNsw lhs rhs) -/
    /- these are definitionally equal, so it's fine anyway and IR.eval is on the outside -/
    let proof := mkApp7 congrLemmaQ nQ lhsExpr rhsExpr lhsEval rhsEval lhsProof rhsProof

    return ⟨ir, irExpr, body, pure proof⟩
