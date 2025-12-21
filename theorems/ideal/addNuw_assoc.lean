import theorems.iN

theorem uaddOverflow_implies_sum {n} {a b c : BitVec n}
    (hab : a.uaddOverflow b)
    (hbc : b.uaddOverflow c = false)
    : a.uaddOverflow (b + c) := by

  have hbc' : ¬b.uaddOverflow c := by simp [hbc]

  have h : (b + c).toNat ≥ b.toNat := by
    rw [BitVec.toNat_add_of_not_uaddOverflow hbc']
    omega

  rw [uaddOverflow_iff_unfold] at ⊢ hab
  omega

theorem addNuw_assoc {n} {x y z : iN n}
    : (x +nuw y) +nuw z = x +nuw (y +nuw z) := by

  poison_unroll x y z => a b c

  by_cases hab : (a.uaddOverflow b)
  case pos =>
    rw [addNuw_uaddOverflow_bitvec hab]
    simp [simp_iN]

    /- b + c no overflow => a + (b + c) overflows -/
    intro h
    exact uaddOverflow_implies_sum hab h

  case neg =>
    by_cases hbc : (b.uaddOverflow c)
    case pos =>
      rw [addNuw_uaddOverflow_bitvec hbc]
      simp [simp_iN]

      /- a + b no overflow => (a + b) + c overflows -/
      intro h
      rw [BitVec.uaddOverflow_comm]
      rw [BitVec.add_comm]

      rw [BitVec.uaddOverflow_comm] at hab hbc

      simp at hab
      exact uaddOverflow_implies_sum hbc hab

    case neg =>
      rw [addNuw_not_uaddOverflow_bitvec_eq_add hab]
      rw [addNuw_not_uaddOverflow_bitvec_eq_add hbc]

      simp [simp_iN]
      constructor
      . simp [BitVec.uaddOverflow_assoc hab hbc]
      . intro h
        rw [← BitVec.uaddOverflow_assoc hab hbc]
        simp [h]
        exact BitVec.add_assoc a b c
