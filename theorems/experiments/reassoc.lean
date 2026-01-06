import theorems.iN
import theorems.Opt
import theorems.Core.Basic

import Qq
open Qq

def reassoc {idx} (ir : IR idx) : IR idx :=
  match ir with
  | .var _ | .const _ | .poison => ir

  /- con + x ~> x + con -/
  | .add (.const val) rhs  =>
    .add (reassoc rhs) (.const val)

  /- (con₁ + x) + con₂ ~> x + (con₁ + con₂) -/
  | .add (.add (.const con₁) x) (.const con₂) =>
    (IR.add (reassoc x) (.const (con₁ + con₂)))

  /- (con + x) + y ~> (x + y) + con) -/
  | .add (.add (.const con) x) y =>
    (IR.add (reassoc x) (reassoc y)).add (.const con)

  | .add (.var id1) (.var id2) =>
    if !(id1 < id2) then
      .add (.var id2) (.var id1)
    else
      ir

  | .add lhs rhs => .add (reassoc lhs) (reassoc rhs)
  | _ => ir

theorem eval_add_comm {idx} (ξ) (σ) (lhs rhs : IR idx)
  : IR.eval ξ σ (IR.add lhs rhs : IR idx) = IR.eval ξ σ (IR.add rhs lhs : IR idx) := by

  unfold IR.eval
  rw [add_comm]

@[simp]
theorem eval_add {idx} (ξ) (σ) (lhs rhs : IR idx)
  : IR.eval ξ σ (IR.add lhs rhs : IR idx) = IR.eval ξ σ lhs + IR.eval ξ σ rhs := by

  conv => lhs; unfold IR.eval

@[simp]
theorem eval_const {idx} (ξ) (σ) (con : Nat)
  : IR.eval ξ σ (IR.const con : IR idx) = ⟦con⟧ := by

  conv => lhs; unfold IR.eval

@[simp high]
theorem bitvec_add_eq_add {n}
    (a b : Nat)
    : ⟦↑(a + b) : n⟧ = ⟦a⟧ + ⟦b⟧ := by

  simp [simp_iN, BitVec.ofNat_add]

attribute [-simp] BitVec.natCast_eq_ofNat

def reassoc' : Rule :=
  { impl := reassoc

  , wf := by
      intros idx ξ σ lhs

      fun_induction reassoc <;> try rfl
      . rename_i ih
        simp; orw [ih]

        rw [add_comm]

      . rename_i ih
        simp; orw [ih]

        conv => rhs; rw [← add_assoc]
        conv => lhs; lhs; rw [add_comm]

      . rename_i ihl ihr
        simp; orw [ihl, ihr]

        rw [add_assoc]
        rw [add_comm]

      . rw [eval_add_comm]
      . rename_i ihl ihr
        simp; orw [ihl, ihr]
  }

theorem example_comm {n} {x : iN n}
    : ((bitvec 4) + x) + x ~> (x + x) + (bitvec 4) := by

  opt reassoc'

theorem example_comm' {n} {x : iN n}
    : ((bitvec 4) + x) + (bitvec 5) ~> x + (bitvec 9) := by

  opt reassoc'
