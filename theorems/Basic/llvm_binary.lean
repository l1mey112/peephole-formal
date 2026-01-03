import theorems.iN

/- # Poison Propagation -/

@[simp high] theorem add_poison_eq_poison : x + poison = poison := by cases x <;> rfl
@[simp high] theorem poison_add_eq_poison : poison + x = poison := by cases x <;> rfl
@[simp high] theorem sub_poison_eq_poison : x - poison = poison := by cases x <;> rfl
@[simp high] theorem poison_sub_eq_poison : poison - x = poison := by cases x <;> rfl
@[simp high] theorem mul_poison_eq_poison : x * poison = poison := by cases x <;> rfl
@[simp high] theorem poison_mul_eq_poison : poison * x = poison := by cases x <;> rfl
@[simp high] theorem sdiv_poison_eq_poison : x /ₛ poison = poison := by cases x <;> rfl
@[simp high] theorem poison_sdiv_eq_poison : poison /ₛ x = poison := by cases x <;> rfl
@[simp high] theorem udiv_poison_eq_poison : x /ᵤ poison = poison := by cases x <;> rfl
@[simp high] theorem poison_udiv_eq_poison : poison /ᵤ x = poison := by cases x <;> rfl
@[simp high] theorem udivExact_poison_eq_poison : x /ᵤexact poison = poison := by cases x <;> rfl
@[simp high] theorem poison_udivExact_eq_poison : poison /ᵤexact x = poison := by cases x <;> rfl
@[simp high] theorem srem_poison_eq_poison : x %ₛ poison = poison := by cases x <;> rfl
@[simp high] theorem poison_srem_eq_poison : poison %ₛ x = poison := by cases x <;> rfl
@[simp high] theorem urem_poison_eq_poison : x %ᵤ poison = poison := by cases x <;> rfl
@[simp high] theorem poison_urem_eq_poison : poison %ᵤ x = poison := by cases x <;> rfl

/- # Basic Lemmas for Add -/

theorem const_add_const : ⟦a⟧ + ⟦b⟧ = ⟦a + b⟧ := by rfl

theorem not_saddOverflow_add_const (h : ¬a.saddOverflow b)
  : ⟦a⟧ +nsw ⟦b⟧ = ⟦a + b⟧ := by simp [simp_iN, h]

theorem saddOverflow_addNsw_eq_poison (h : a.saddOverflow b)
  : ⟦a⟧ +nsw ⟦b⟧ = poison := by simp [simp_iN, h]

theorem not_uaddOverflow_addNuw_eq_poison (h : ¬a.uaddOverflow b)
  : ⟦a⟧ +nuw ⟦b⟧ = ⟦a + b⟧ := by simp [simp_iN, h]

theorem uaddOverflow_addNuw_eq_poison (h : a.uaddOverflow b)
  : ⟦a⟧ +nuw ⟦b⟧ = poison := by simp [simp_iN, h]

theorem not_saddOverflow_not_uaddOverflow_addNw_eq_const
  (hs : ¬a.saddOverflow b) (hu : ¬a.uaddOverflow b)
  : ⟦a⟧ +nw ⟦b⟧ = ⟦a + b⟧ := by simp [simp_iN, hs, hu]

theorem not_saddOverFlow_addNw_eq_addNsw (h : ¬a.saddOverflow b)
  : ⟦a⟧ +nw ⟦b⟧ = ⟦a⟧ +nuw ⟦b⟧ := by simp [simp_iN, h]

theorem not_uaddOverFlow_addNw_eq_addNuw (h : ¬a.uaddOverflow b)
  : ⟦a⟧ +nw ⟦b⟧ = ⟦a⟧ +nsw ⟦b⟧ := by simp [simp_iN, h]

theorem saddOverflow_addNw_eq_poison (h : a.saddOverflow b)
  : ⟦a⟧ +nw ⟦b⟧ = poison := by simp [simp_iN, h]

theorem uaddOverflow_addNw_eq_poison (h : a.uaddOverflow b)
  : ⟦a⟧ +nw ⟦b⟧ = poison := by simp [simp_iN, h]

/- # Refinement Lemmas for Add -/

theorem addNsw_refine : x +nsw y ~> x + y := by poison_unroll' x y
theorem addNuw_refine : x +nuw y ~> x + y := by poison_unroll' x y
theorem addNw_refine  : x +nw y ~> x + y := by poison_unroll' x y

theorem addNw_refine_addNsw : x +nw y ~> x +nuw y := by
  poison_unroll x y => a b
  by_cases h : a.saddOverflow b
  . rw [saddOverflow_addNw_eq_poison (show a.saddOverflow b by simp [h])]
    apply Rewrite.poison_rewrite
  · rw [not_saddOverFlow_addNw_eq_addNsw (show ¬a.saddOverflow b by simp [h])]

theorem addNw_refine_addNuw : x +nw y ~> x +nsw y := by
  poison_unroll x y => a b
  by_cases h : a.uaddOverflow b
  . rw [uaddOverflow_addNw_eq_poison (show a.uaddOverflow b by simp [h])]
    apply Rewrite.poison_rewrite
  · rw [not_uaddOverFlow_addNw_eq_addNuw (show ¬a.uaddOverflow b by simp [h])]

/- # Basic Lemmas for Sub -/

theorem const_sub_const : ⟦a⟧ - ⟦b⟧ = ⟦a - b⟧ := by rfl

theorem not_ssubOverflow_subNsw_eq_const (h : ¬a.ssubOverflow b)
  : ⟦a⟧ -nsw ⟦b⟧ = ⟦a - b⟧ := by simp [simp_iN, h]

theorem ssubOverflow_subNsw_eq_poison (h : a.ssubOverflow b)
  : ⟦a⟧ -nsw ⟦b⟧ = poison := by simp [simp_iN, h]

theorem not_usubOverflow_subNuw_eq_const (h : ¬a.usubOverflow b)
  : ⟦a⟧ -nuw ⟦b⟧ = ⟦a - b⟧ := by simp [simp_iN, h]

theorem usubOverflow_subNuw_eq_poison (h : a.usubOverflow b)
  : ⟦a⟧ -nuw ⟦b⟧ = poison := by simp [simp_iN, h]

theorem not_ssubOverflow_not_usubOverflow_subNw_eq_const
  (hs : ¬a.ssubOverflow b) (hu : ¬a.usubOverflow b)
  : ⟦a⟧ -nw ⟦b⟧ = ⟦a - b⟧ := by simp [simp_iN, hs, hu]

theorem not_ssubOverFlow_subNw_eq_subNsw (h : ¬a.ssubOverflow b)
  : ⟦a⟧ -nw ⟦b⟧ = ⟦a⟧ -nuw ⟦b⟧ := by simp [simp_iN, h]

theorem not_usubOverFlow_subNw_eq_subNuw (h : ¬a.usubOverflow b)
  : ⟦a⟧ -nw ⟦b⟧ = ⟦a⟧ -nsw ⟦b⟧ := by simp [simp_iN, h]

theorem ssubOverflow_subNw_eq_poison (h : a.ssubOverflow b)
  : ⟦a⟧ -nw ⟦b⟧ = poison := by simp [simp_iN, h]

theorem usubOverflow_subNw_eq_poison (h : a.usubOverflow b)
  : ⟦a⟧ -nw ⟦b⟧ = poison := by simp [simp_iN, h]

/- # Refinement Lemmas for Sub -/

theorem subNsw_refine : x -nsw y ~> x - y := by poison_unroll' x y
theorem subNuw_refine : x -nuw y ~> x - y := by poison_unroll' x y
theorem subNw_refine  : x -nw y ~> x - y := by poison_unroll' x y

theorem subNw_refine_subNsw : x -nw y ~> x -nuw y := by
  poison_unroll x y => a b
  by_cases h : a.ssubOverflow b
  . rw [ssubOverflow_subNw_eq_poison (show a.ssubOverflow b by simp [h])]
    apply Rewrite.poison_rewrite
  · rw [not_ssubOverFlow_subNw_eq_subNsw (show ¬a.ssubOverflow b by simp [h])]

theorem subNw_refine_subNuw : x -nw y ~> x -nsw y := by
  poison_unroll x y => a b
  by_cases h : a.usubOverflow b
  . rw [usubOverflow_subNw_eq_poison (show a.usubOverflow b by simp [h])]
    apply Rewrite.poison_rewrite
  · rw [not_usubOverFlow_subNw_eq_subNuw (show ¬a.usubOverflow b by simp [h])]

/- # Basic Lemmas for Mul -/

theorem const_mul_const : ⟦a⟧ * ⟦b⟧ = ⟦a * b⟧ := by rfl

theorem not_smulOverflow_mulNsw_eq_const (h : ¬a.smulOverflow b)
  : ⟦a⟧ *nsw ⟦b⟧ = ⟦a * b⟧ := by simp [simp_iN, h]

theorem smulOverflow_mulNsw_eq_poison (h : a.smulOverflow b)
  : ⟦a⟧ *nsw ⟦b⟧ = poison := by simp [simp_iN, h]

theorem not_umulOverflow_mulNuw_eq_const (h : ¬a.umulOverflow b)
  : ⟦a⟧ *nuw ⟦b⟧ = ⟦a * b⟧ := by simp [simp_iN, h]

theorem umulOverflow_mulNuw_eq_poison (h : a.umulOverflow b)
  : ⟦a⟧ *nuw ⟦b⟧ = poison := by simp [simp_iN, h]

theorem not_smulOverflow_not_umulOverflow_mulNw_eq_const
  (hs : ¬a.smulOverflow b) (hu : ¬a.umulOverflow b)
  : ⟦a⟧ *nw ⟦b⟧ = ⟦a * b⟧ := by simp [simp_iN, hs, hu]

theorem not_smulOverFlow_mulNw_eq_mulNsw (h : ¬a.smulOverflow b)
  : ⟦a⟧ *nw ⟦b⟧ = ⟦a⟧ *nuw ⟦b⟧ := by simp [simp_iN, h]

theorem not_umulOverFlow_mulNw_eq_mulNuw (h : ¬a.umulOverflow b)
  : ⟦a⟧ *nw ⟦b⟧ = ⟦a⟧ *nsw ⟦b⟧ := by simp [simp_iN, h]

theorem smulOverflow_mulNw_eq_poison (h : a.smulOverflow b)
  : ⟦a⟧ *nw ⟦b⟧ = poison := by simp [simp_iN, h]

theorem umulOverflow_mulNw_eq_poison (h : a.umulOverflow b)
  : ⟦a⟧ *nw ⟦b⟧ = poison := by simp [simp_iN, h]

/- # Refinement Lemmas for Mul -/

theorem mulNsw_refine : x *nsw y ~> x * y := by poison_unroll' x y
theorem mulNuw_refine : x *nuw y ~> x * y := by poison_unroll' x y
theorem mulNw_refine  : x *nw y ~> x * y := by poison_unroll' x y

theorem mulNw_refine_mulNsw : x *nw y ~> x *nuw y := by
  poison_unroll x y => a b
  by_cases h : a.smulOverflow b
  . rw [smulOverflow_mulNw_eq_poison (show a.smulOverflow b by simp [h])]
    apply Rewrite.poison_rewrite
  · rw [not_smulOverFlow_mulNw_eq_mulNsw (show ¬a.smulOverflow b by simp [h])]

theorem mulNw_refine_mulNuw : x *nw y ~> x *nsw y := by
  poison_unroll x y => a b
  by_cases h : a.umulOverflow b
  . rw [umulOverflow_mulNw_eq_poison (show a.umulOverflow b by simp [h])]
    apply Rewrite.poison_rewrite
  · rw [not_umulOverFlow_mulNw_eq_mulNuw (show ¬a.umulOverflow b by simp [h])]

/- # Basic Lemmas for Div -/

theorem const_sdiv_const_rewrite : ⟦a⟧ /ₛ ⟦b⟧ ~> ⟦a.sdiv b⟧ := by simp [simp_iN]

theorem sdiv_zero_eq_poison
  : x /ₛ ⟦0⟧ = poison := by simp [simp_iN]

theorem intMin_sdiv_neg_one_eq_poison
  : ⟦BitVec.intMin n⟧ /ₛ ⟦-1⟧ = poison := by simp [simp_iN]

theorem const_udiv_const_rewrite : ⟦a⟧ /ᵤ ⟦b⟧ ~> ⟦a.udiv b⟧ := by simp [simp_iN]

theorem udiv_zero_eq_poison
  : x /ᵤ ⟦0⟧ = poison := by simp [simp_iN]

theorem udiv_nonzero (h : b ≠ 0)
  : ⟦a⟧ /ᵤ ⟦b⟧ = ⟦a.udiv b⟧ := by simp_all [simp_iN]

theorem const_udivExact_const_rewrite : ⟦a⟧ /ᵤexact ⟦b⟧ ~> ⟦a.udiv b⟧ := by simp [simp_iN]

theorem udivExact_zero_eq_poison
  : x /ᵤexact ⟦0⟧ = poison := by simp [simp_iN]

theorem udivExact_inexact_eq_poison (h : a % b != 0)
  : ⟦a⟧ /ᵤexact ⟦b⟧ = poison := by simp_all [simp_iN]

/- # Refinement Lemmas for Div -/

theorem udivExact_refine : x /ᵤexact y ~> x /ᵤ y := by
  poison_unroll x y => a b

  by_cases h : a % b != 0
  . rw [udivExact_inexact_eq_poison h]
    apply Rewrite.poison_rewrite

  by_cases hz : b = 0
  . rw [hz, udivExact_zero_eq_poison]
    apply Rewrite.poison_rewrite

  . simp_all [simp_iN]
