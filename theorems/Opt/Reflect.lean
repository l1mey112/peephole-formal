import theorems.Opt.Basic

namespace IR

theorem eval_var' {idx id} (ξ : WidthAssignment) (σ : Assignment) (x : iN (ξ.get idx))
  (hb : (σ.get id).n = ξ.get idx)
  (h : hb ▸ (σ.get id).x = x)
  : IR.eval ξ σ (IR.var id : IR idx) = x := by

  simp [IR.eval, h, hb]

@[simp]
theorem eval_var {idx id} (ξ : WidthAssignment) (σ : Assignment)
  : IR.eval ξ σ (IR.var id : IR idx) = (σ.get id).truncate (ξ.get idx) := by

  grind [IR.eval, PackediN.truncate]

end IR

theorem addNsw_congr (n : Nat) (lhs rhs lhs' rhs' : iN n) (h1 : lhs' = lhs) (h2 : rhs' = rhs)
    : lhs' +nsw rhs' = lhs +nsw rhs := by simp_all

theorem add_congr (n : Nat) (lhs rhs lhs' rhs' : iN n) (h1 : lhs' = lhs) (h2 : rhs' = rhs)
    : lhs' + rhs' = lhs + rhs := by simp_all
