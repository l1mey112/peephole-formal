import theorems.iN

import Lean
import Qq
open Lean Elab Meta
open Qq

inductive IR : Nat → Type where
  | var (id : Nat) : IR idx
  | const (val : Nat) : IR idx
  | const_poison : IR idx

  | add (lhs rhs : IR idx) : IR idx
  | addNsw (lhs rhs : IR idx) : IR idx
deriving BEq, Repr, ToExpr

deriving instance BEq for iN

structure PackediN where
  {n : Nat}
  x : iN n
deriving BEq

def PackediN.truncate (pack : PackediN) (n : Nat) : iN n :=
  match pack.x with
  | poison => poison
  | bitvec a => a.truncate n

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

  | const val => bitvec val
  | const_poison => poison

  | add lhs rhs => iN.add (eval ξ σ lhs) (eval ξ σ rhs)
  | addNsw lhs rhs => iN.addNsw (eval ξ σ lhs) (eval ξ σ rhs)

  /- | add lhs rhs => iN.add (eval σ lhs) (eval σ rhs)
  | addNsw lhs rhs => iN.addNsw (eval σ lhs) (eval σ rhs)
  | addNuw lhs rhs => iN.addNuw (eval σ lhs) (eval σ rhs)
  | addNw lhs rhs => iN.addNw (eval σ lhs) (eval σ rhs) -/

end IR

theorem add_zero {n} (x : iN n) : x + (bitvec 0) ~> x := by
  poison_unroll x => a
  simp [simp_iN]

/--
For the implementation to optimise, it needs to know whether or not the width assignment respect the `valid` prop.
--/
structure Rule where
  valid : WidthAssignment → Bool

  impl : {idx : Nat} → IR idx → IR idx

  wf : ∀ (ξ : WidthAssignment) (ξvalid : valid ξ) (σ : Assignment) {idx : Nat} (lhs : IR idx),
    let rhs := impl lhs
    (IR.eval ξ σ lhs) ~> (IR.eval ξ σ rhs)

def add_zero' : Rule :=
  { valid := fun ξ => true
  , impl := fun ir => match ir with
      | IR.add lhs (IR.const 0) => lhs
      | _ => ir
  , wf := by
      intros ξ _ σ _ lhs

      split <;> try rfl
      apply add_zero
  }

def applyRewrite {idx} (ir : IR idx) (r : Rule) : IR idx :=
  r.impl ir

theorem applyRewriteCorrect (ir : IR idx) (r : Rule)
  (σ : Assignment) (ξ : WidthAssignment) (ξvalid : r.valid ξ)
  : (IR.eval ξ σ ir) ~> (IR.eval ξ σ (applyRewrite ir r)) := r.wf ξ ξvalid σ ir

def A : IR 0 := IR.add (IR.var 0) (IR.const 0)
def B : IR 0 := applyRewrite A add_zero'

def Aeval {n} : iN n → iN n :=
  fun x => IR.eval (Lean.RArray.leaf n) (Lean.RArray.leaf ⟨x⟩) A

def Beval {n} : iN n → iN n :=
  fun x => IR.eval (Lean.RArray.leaf n) (Lean.RArray.leaf ⟨x⟩) B

theorem Aeval_rewrite_Beval {n} (x : iN n) :
  Aeval x ~> Beval x :=
  applyRewriteCorrect A add_zero' (Lean.RArray.leaf ⟨x⟩) (Lean.RArray.leaf n) (by trivial)

#eval @Aeval 32 (bitvec 1)

theorem addNsw_refine_add {n} (x y : iN n) : x +nsw y ~> x + y := by
  poison_unroll x y => a b

  by_cases h : a.saddOverflow b
  . rw [addNsw_saddOverflow_bitvec h]
    exact Rewrite.poison_rewrite (bitvec a + bitvec b)
  . rw [addNsw_not_saddOverflow_bitvec_eq_add h]
    simp [simp_iN]

def addNsw_refine_add' : Rule :=
  { valid := fun ξ => true
  , impl := fun ir => match ir with
      | IR.addNsw lhs rhs => IR.add lhs rhs
      | _ => ir

  , wf := by
      intros ξ _ σ _ lhs

      split <;> try rfl
      apply addNsw_refine_add
  }

def Cσ (x y : iN n) : Assignment :=
  .ofArray #[⟨x⟩, ⟨y⟩] (by simp)

/- program C is optimised into program D -/
def C : IR 0 := IR.addNsw (IR.var 0) (IR.var 1)
def D : IR 0 := applyRewrite C addNsw_refine_add'

/- Ceval is the actual denoted semantics behind C, same for Deval -/
def Ceval {n} (x y : iN n) : iN n := IR.eval (.leaf n) (Cσ x y) C
def Deval {n} (x y : iN n) : iN n := IR.eval (.leaf n) (Cσ x y) D

/- correctness proof -/
theorem Ceval_rewrite_Deval {n} (x y : iN n) :
  Ceval x y ~> Deval x y :=
  applyRewriteCorrect C addNsw_refine_add' (Cσ x y) (.leaf n) (by trivial)

/- but, behaviour is not equal! the behaviour of C is "refined" into D -/
#eval @Ceval 32 (bitvec 2147483647) (bitvec 1) /- iN.poison -/
#eval @Deval 32 (bitvec 2147483647) (bitvec 1) /- iN.bitvec 0x80000000#32 -/

/- ----------------------------------------------------------------- -/

partial def reifyIRExpr (idx : Nat) (assignment : Array (FVarId × Nat)) (body : Expr) : MetaM (IR idx) := do
  match_expr body with
  | iN.poison _ => return IR.const_poison
  | iN.bitvec _ e =>
    if let some (v, _) := (← getOfNatValue? e ``BitVec) then
      return IR.const v

    throwError "reifyIRExpr: unsupported bitvec expression {body}"

  | iN.add _ lhs rhs =>
    let lhs_ir ← reifyIRExpr idx assignment lhs
    let rhs_ir ← reifyIRExpr idx assignment rhs
    return IR.add lhs_ir rhs_ir
  | iN.addNsw _ lhs rhs =>
    let lhs_ir ← reifyIRExpr idx assignment lhs
    let rhs_ir ← reifyIRExpr idx assignment rhs
    return IR.addNsw lhs_ir rhs_ir
  | _ =>

    if let some fvarid := body.fvarId? then
      let some varIdx := assignment.findIdx? (fun (fid, _) => fid == fvarid)
        | throwError "reifyIRExpr: unbound free variable {body}"

      return IR.var varIdx

    throwError "reifyIRExpr: unsupported expression {body}"

structure PackedIR where
  {idx : Nat}
  ir : IR idx
deriving Repr

def reifyExprApply (rule : Rule) (ruleExpr : Q(Rule)) (e : Expr) : MetaM PackedIR := do
  /- doesn't support hypotheses such as `fun {n} {m} (h : m ≤ n) (x : iN n) : iN m := ...`,
    hence valid is just set to returning true always -/

  lambdaTelescope e fun fvars body => do

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

    let ir ← reifyIRExpr resultIdx assignment body

    have resultIdxQ : Q(Nat) := toExpr resultIdx
    have irQ : Q(IR $resultIdxQ) := toExpr ir

    let assignment' : RArray (FVarId × Nat) :=
      RArray.ofArray assignment (by exact Decidable.of_not_not h)

    let width_assignment' : RArray FVarId :=
      RArray.ofArray width_assignment (by exact Decidable.of_not_not h')

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

    let proof := q(@applyRewriteCorrect $resultIdxQ $irQ $ruleExpr $σQ $ξQ sorry)
    check proof

    logInfo m!"proof: {proof}"
    let proofType ← inferType proof

    match_expr proofType with
    | Rewrite _ lhs rhs =>
      logInfo m!"lhs: {← reduceAll lhs}"
      logInfo m!"rhs: {← reduceAll rhs}"
    | _ => pure ()

    /- let ⟨_, ~q(Rewrite $n $lhs $rhs), ~q($e)⟩ ← inferTypeQ proof | throwError "reifyExprApply: unexpected proof type"
 -/
    logInfo m!"proofType: {proofType}"

    /- let proofReduced ← reduce proofType
    logInfo m!"proofTypeReduced: {proofReduced}" -/


    return ⟨rule.impl ir⟩

unsafe def evalPleaseImpl (expr : Expr) : MetaM Rule :=
  evalExpr Rule q(Rule) expr

@[implemented_by evalPleaseImpl]
opaque evalPlease (expr : Expr) : MetaM Rule

syntax rwRuleSeq := "[" withoutPosition(term,*,?) "]"

/- accepts expressions of the form
  `fun {n} ... {m} (x : iN n) ... (z : iN m) : iN n => ...` -/
elab "⟪" t:term "⟫" s:rwRuleSeq : term => do
  let t ← Term.elabTerm t none

  match s with
  | `(rwRuleSeq| [$rs,*]) =>
    let rewrites ← Term.withoutErrToSorry do
      let rewrites ← rs.getElems.mapM fun te => Term.elabTermEnsuringType te q(Rule)
      MetaM.run' (rewrites.mapM evalPlease)

    logInfo m!"rewrites: {rewrites.size}"

    /- TODO handle other rewrites -/
    let irExpr ← reifyExprApply addNsw_refine_add' q(addNsw_refine_add') t
    logInfo m!"reified IR: {repr irExpr}"

    return t
  | _ => throwUnsupportedSyntax


--#eval ⟪fun {n} {m} (x : iN n) (y : iN m) => y⟫
def fn := ⟪fun {n} (x : iN n) => x +nsw x⟫ []

#print fn
