import theorems.iN

/- # Poison Propagation -/

@[simp high] theorem shl_poison_eq_poison : x << poison = poison := by cases x <;> rfl
@[simp high] theorem poison_shl_eq_poison : poison << x = poison := by cases x <;> rfl
@[simp high] theorem shlNsw_poison_eq_poison : x <<nsw poison = poison := by cases x <;> rfl
@[simp high] theorem poison_shlNsw_eq_poison : poison <<nsw x = poison := by cases x <;> rfl
@[simp high] theorem shlNuw_poison_eq_poison : x <<nuw poison = poison := by cases x <;> rfl
@[simp high] theorem poison_shlNuw_eq_poison : poison <<nuw x = poison := by cases x <;> rfl
@[simp high] theorem lshr_poison_eq_poison : x >>ᵤ poison = poison := by cases x <;> rfl
@[simp high] theorem poison_lshr_eq_poison : poison >>ᵤ x = poison := by cases x <;> rfl
@[simp high] theorem lshrExact_poison_eq_poison : x >>ᵤexact poison = poison := by cases x <;> rfl
@[simp high] theorem poison_lshrExact_eq_poison : poison >>ᵤexact x = poison := by cases x <;> rfl
@[simp high] theorem ashr_poison_eq_poison : x >>ₛ poison = poison := by cases x <;> rfl
@[simp high] theorem poison_ashr_eq_poison : poison >>ₛ x = poison := by cases x <;> rfl
@[simp high] theorem ashrExact_poison_eq_poison : x >>ₛexact poison = poison := by cases x <;> rfl
@[simp high] theorem poison_ashrExact_eq_poison : poison >>ₛexact x = poison := by cases x <;> rfl
@[simp high] theorem and_poison_eq_poison : (x : iN n) &&& (poison : iN n) = poison := by cases x <;> rfl
@[simp high] theorem poison_and_eq_poison : (poison : iN n) &&& (x : iN n) = poison := by cases x <;> rfl
@[simp high] theorem or_poison_eq_poison : (x : iN n) ||| (poison : iN n) = poison := by cases x <;> rfl
@[simp high] theorem poison_or_eq_poison : (poison : iN n) ||| (x : iN n) = poison := by cases x <;> rfl
@[simp high] theorem not_poison_eq_poison : ~~~(poison : iN n) = poison := by rfl
@[simp high] theorem xor_poison_eq_poison : (x : iN n) ^^^ (poison : iN n) = poison := by cases x <;> rfl
@[simp high] theorem poison_xor_eq_poison : (poison : iN n) ^^^ (x : iN n) = poison := by cases x <;> rfl

/- # Basic Lemmas for Shift -/

theorem const_shl : ⟦a : n⟧ << ⟦b⟧ ~> ⟦a <<< b⟧ := by
  by_cases h : n = 0
  . subst h; simp [simp_iN]
  . simp [simp_iN, h]



/- theorem not_lt_width_shl_const_eq_poison (hn : n ≥ 1) {b : BitVec n}
    /- (h : ¬b.toNat < n) -/
    /- (h : LtWidth b) -/
    : x << ⟦b⟧ = poison := by


  have : ¬n = 0 := by grind
  have : n ≤ b := by


    refine BitVec.le_of_lt ?_

    simp_all
    rw [BitVec.toNat_lt]


  simp_all [simp_iN]


  sorry -/
