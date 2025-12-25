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
deriving BEq, Repr

structure PackedIR where
  {idx : Nat}
  x : IR idx
deriving BEq, Repr

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

theorem addNsw_refine_add {n} (x y : iN n) : x +nsw y ~> x + y := by
  poison_unroll x y => a b

  by_cases h : a.saddOverflow b
  . rw [addNsw_saddOverflow_bitvec h]
    exact Rewrite.poison_rewrite (bitvec a + bitvec b)
  . rw [addNsw_not_saddOverflow_bitvec_eq_add h]
    simp [simp_iN]

structure IRRewrite where
  valid : WidthAssignment → Bool

  lhs : IR 0
  impl : (ξ : WidthAssignment) → valid ξ → IR 0 → IR 0

  wf : ∀ (ξ : WidthAssignment) (h : valid ξ) (σ : Assignment),
    let rhs := impl ξ h lhs
    (IR.eval ξ σ lhs) ~> (IR.eval ξ σ rhs)

def addNsw_refine_add' : IRRewrite :=
  { valid := fun ξ => true
  , lhs := IR.addNsw (IR.var 0) (IR.var 1)
  , impl := fun ξ _ ir => IR.add (IR.var 0) (IR.var 1)
  , wf := by
      intros ξ _ σ
      apply addNsw_refine_add
  }

theorem add_zero {n} (x : iN n) : x + (bitvec 0) ~> x := by
  poison_unroll x => a
  simp [simp_iN]

def add_zero' : IRRewrite :=
  { valid := fun ξ => true
  , lhs := IR.add (IR.var 0) (IR.const 0)
  , impl := fun ξ _ ir => IR.var 0
  , wf := by
      intros ξ _ σ
      apply add_zero
  }

structure MatchState where
  assignment : Array PackedIR
deriving Inhabited, Repr

abbrev MatchM := StateT MatchState Option

/- construct a new WidthAssignment after the match happens, then return some (ξ, σ) if match -/
def MatchM.match (lhs ir : IR idx) : MatchM Unit := do
  match lhs, ir with
  | .var id, _ =>
    let st ← get
    if let some ir_existing := st.assignment[id]? then
      if h : ir_existing.idx = idx then
        let ir_existing : IR idx := h ▸ ir_existing.x

        if ir_existing == ir then
          return ()

      failure

    else if id == st.assignment.size then
      /- extend the assignment -/
      let new_assignment := st.assignment.push ⟨ir⟩
      modify fun s => { s with assignment := new_assignment }
    else
      failure

  | .addNsw lhs rhs, .addNsw lhs' rhs' =>
    MatchM.match lhs lhs'
    MatchM.match rhs rhs'
    return ()

  | _, _ => failure

def matchRewriteAbstract {n} (lhs ir : IR n) : Option MatchState :=
  let result := (MatchM.match lhs ir).run default
  match result with
  | some ((), st) => some st
  | none => none

#eval matchRewriteAbstract
  (IR.addNsw (IR.var 0) (IR.var 1) : IR 0)
  (IR.addNsw (IR.const 10) (IR.const 23) : IR 0)

/- def matchRewrite {n} (σ : IR.Assignment) (ir : IR n) (r : IRRewrite) : Bool :=
  let ξ : WidthAssignment := Lean.RArray.leaf n
  if h : r.valid ξ then
    let lhs' : IR n := r.lhs ξ h

    /- abstract lhs over lhs' -/

    sorry
  else
    false -/


  /- match ir with
  | .addNsw lhs rhs =>
    let ξ : WidthAssignment := Lean.RArray.ofArray #[n] (by simp)
    /- lhs is (IR.var 0), rhs is (IR.var 1) -/
    let σᵢ : IR.Assignment :=
      Lean.RArray.ofArray #[⟨IR.eval σ lhs⟩, ⟨IR.eval σ rhs⟩] (by simp)

    if h : r.valid ξ then
      let lhs' := r.lhs ξ h

      sorry
    else
      false
  | _ => false

/- def runRewrite {n} (ir : IR n) (r :  IRRewrite) (ξ : WidthAssignment) (h : r.valid ξ) : IR n :=
  r.impl ξ h (r.lhs ξ h) -/

/- def wa :=
  let ξ : WidthAssignment := Lean.RArray.ofArray #[8] (by decide)
  /- have t := addNsw_refine_add'.valid wa -/

  have t : addNsw_refine_add'.valid ξ = true := by
    rfl

  let lhs := addNsw_refine_add'.lhs ξ t

  sorry -/

  /- Lean.RArray.ofArray #[8] (by decide)

have t := addNsw_refine_add'.valid wa
 -/
/- def t : List IRRewrite := [addNsw_refine_add']

#eval addNsw_refine_add'.valid -/

/- theorem addNsw_refine_add {n} (x y : iN n) : x +nsw y ~> x + y := by

 -/
/- inductive IRe : Nat → Type where
  | const {n : Nat} (val : BitVec n) : IR n
  | sext {n : Nat} (w : Nat) (arg : IR w) : IR n -/

-- ∀x : α, P x ↔ (x : α) → P x

/- syntax "⟦" term "⟧" : term /- denote -/
syntax "⟪" term "⟫" : term /- convert to expr -/

/- macro_rules
| `(⟦$term⟧) => `(IR.eval $term)
| `(⟪$term⟫) => `(IR.eval $term) -/

/- will convert a proof of lhs ~> rhs into a proper rewrite -/
elab "⟪" stx:term "⟫" : term => do

  have qir : Q(Prop) := ← Term.elabTerm stx none
  let ⟨⟩ ← match qir with
  | ~q(@Rewrite $n $lhs $rhs) => sorry
  | ~q($lhs = $rhs) => sorry
  | _ => throwError "expected a Rewrite structure"

  `(IR.eval $ir) -/
-/
