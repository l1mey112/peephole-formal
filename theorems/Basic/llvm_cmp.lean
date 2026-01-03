import theorems.iN

/- # Poison Propagation -/

@[simp high] theorem icmpEq_poison_eq_poison : (x ==' poison) = poison := by cases x <;> rfl
@[simp high] theorem poison_icmpEq_eq_poison : (poison ==' x) = poison := by cases x <;> rfl
@[simp high] theorem icmpNe_poison_eq_poison : (x !=' poison) = poison := by cases x <;> rfl
@[simp high] theorem poison_icmpNe_eq_poison : (poison !=' x) = poison := by cases x <;> rfl
@[simp high] theorem icmpUgt_poison_eq_poison : (x >ᵤ poison) = poison := by cases x <;> rfl
@[simp high] theorem poison_icmpUgt_eq_poison : (poison >ᵤ x) = poison := by cases x <;> rfl
@[simp high] theorem icmpUge_poison_eq_poison : (x ≥ᵤ poison) = poison := by cases x <;> rfl
@[simp high] theorem poison_icmpUge_eq_poison : (poison ≥ᵤ x) = poison := by cases x <;> rfl
@[simp high] theorem icmpUlt_poison_eq_poison : (x <ᵤ poison) = poison := by cases x <;> rfl
@[simp high] theorem poison_icmpUlt_eq_poison : (poison <ᵤ x) = poison := by cases x <;> rfl
@[simp high] theorem icmpUle_poison_eq_poison : (x ≤ᵤ poison) = poison := by cases x <;> rfl
@[simp high] theorem poison_icmpUle_eq_poison : (poison ≤ᵤ x) = poison := by cases x <;> rfl
@[simp high] theorem icmpSgt_poison_eq_poison : (x >ₛ poison) = poison := by cases x <;> rfl
@[simp high] theorem poison_icmpSgt_eq_poison : (poison >ₛ x) = poison := by cases x <;> rfl
@[simp high] theorem icmpSge_poison_eq_poison : (x ≥ₛ poison) = poison := by cases x <;> rfl
@[simp high] theorem poison_icmpSge_eq_poison : (poison ≥ₛ x) = poison := by cases x <;> rfl
@[simp high] theorem icmpSlt_poison_eq_poison : (x <ₛ poison) = poison := by cases x <;> rfl
@[simp high] theorem poison_icmpSlt_eq_poison : (poison <ₛ x) = poison := by cases x <;> rfl
@[simp high] theorem icmpSle_poison_eq_poison : (x ≤ₛ poison) = poison := by cases x <;> rfl
@[simp high] theorem poison_icmpSle_eq_poison : (poison ≤ₛ x) = poison := by cases x <;> rfl
