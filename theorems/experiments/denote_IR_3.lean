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

  impl : (ξ : WidthAssignment) → valid ξ → {idx : Nat} → IR idx → IR idx

  wf : ∀ (ξ : WidthAssignment) (h : valid ξ) (σ : Assignment) {idx : Nat} (lhs : IR idx),
    let rhs := impl ξ h lhs
    (IR.eval ξ σ lhs) ~> (IR.eval ξ σ rhs)

def add_zero' : Rule :=
  { valid := fun ξ => true
  , impl := fun ξ _ _ ir => match ir with
      | IR.add lhs (IR.const 0) => lhs
      | _ => ir
  , wf := by
      intros ξ _ σ _ lhs

      split <;> try rfl
      apply add_zero
  }

def applyRewrite {idx} (ir : IR idx) (r : Rule) (ξ : WidthAssignment) (ξvalid : r.valid ξ) : IR idx :=
  r.impl ξ ξvalid ir

theorem applyRewriteCorrect (ir : IR idx) (r : Rule)
  (σ : Assignment) (ξ : WidthAssignment) (ξvalid : r.valid ξ)
  : (IR.eval ξ σ ir) ~> (IR.eval ξ σ (applyRewrite ir r ξ ξvalid)) := r.wf ξ ξvalid σ ir

def A : IR 0 := IR.add (IR.var 0) (IR.const 0)
def B {n : Nat} : IR 0 := applyRewrite A add_zero' (Lean.RArray.leaf n) (by trivial)

def Aeval {n} : iN n → iN n :=
  fun x => IR.eval (Lean.RArray.leaf n) (Lean.RArray.leaf ⟨x⟩) A

def Beval {n} : iN n → iN n :=
  fun x => IR.eval (Lean.RArray.leaf n) (Lean.RArray.leaf ⟨x⟩) (@B n)

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
  , impl := fun ξ _ _ ir => match ir with
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
def D {n : Nat} : IR 0 := applyRewrite C addNsw_refine_add' (.leaf n) (by trivial)

/- Ceval is the actual denoted semantics behind C, same for Deval -/
def Ceval {n} (x y : iN n) : iN n := IR.eval (.leaf n) (Cσ x y) C
def Deval {n} (x y : iN n) : iN n := IR.eval (.leaf n) (Cσ x y) (@D n)

/- correctness proof -/
theorem Ceval_rewrite_Deval {n} (x y : iN n) :
  Ceval x y ~> Deval x y :=
  applyRewriteCorrect C addNsw_refine_add' (Cσ x y) (.leaf n) (by trivial)

/- but, behaviour is not equal! the behaviour of C is "refined" into D -/
#eval @Ceval 32 (bitvec 2147483647) (bitvec 1) /- iN.poison -/
#eval @Deval 32 (bitvec 2147483647) (bitvec 1) /- iN.bitvec 0x80000000#32 -/
