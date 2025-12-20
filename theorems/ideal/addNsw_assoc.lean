import theorems.iN

theorem saddOverflow_pos_implies_sum {n} {a b c : BitVec n}
  (hxyz : 0 ≤ a.toInt ∧ 0 ≤ b.toInt ∧ 0 ≤ c.toInt
    ∨ a.toInt ≤ 0 ∧ b.toInt ≤ 0 ∧ c.toInt ≤ 0)

  (hab : a.saddOverflow b)
  (hbc : b.saddOverflow c = false)
  : a.saddOverflow (b + c) := by

  /- (b + c).toInt ≥ b.toInt -/

  have hbc' : ¬b.saddOverflow c := by simp [hbc]

  cases hxyz
  . have h : (b + c).toInt ≥ b.toInt := by
      rw [BitVec.toInt_add_of_not_saddOverflow hbc']
      omega

    rw [saddOverflow_iff_or]; left
    rw [saddOverflow_iff_or] at hab
    obtain habl | habr := hab <;> omega

  . have h : (b + c).toInt ≤ b.toInt := by
      rw [BitVec.toInt_add_of_not_saddOverflow hbc']
      omega

    rw [saddOverflow_iff_or]; right
    rw [saddOverflow_iff_or] at hab

    obtain habl | habr := hab;
    . /- contradiction, by assumption -/
      have upper_bound_gt_1 : a.toInt + b.toInt ≥ 1 := by
        calc 1
          ≤ 2 ^ (n - 1)         := by exact_mod_cast Nat.one_le_two_pow
          _ ≤ a.toInt + b.toInt := habl
      omega
    . omega

theorem addNsw_assoc_same_sign {n} {x y z : iN n}
    (hxyz : x ∈ i[0,∞]  ∧ y ∈ i[0,∞]  ∧ z ∈ i[0,∞]
          ∨ x ∈ i[-∞,0] ∧ y ∈ i[-∞,0] ∧ z ∈ i[-∞,0])

    : (x +nsw y) +nsw z = x +nsw (y +nsw z) := by

  poison_unroll x y z => a b c

  /- case 1. (a + b) + c overflow ↔ a + (b + c) overflow -/
  /- case 2. none of them overflow -/

  by_cases hab : (a.saddOverflow b)
  case pos =>
    /- overflow => poison -/
    rw [addNsw_saddOverflow_bitvec hab]
    simp [simp_iN]

    /- b + c no overflow => a + (b + c) overflows -/
    intro hbc
    exact saddOverflow_pos_implies_sum hxyz hab hbc

  case neg =>
    by_cases hbc : (b.saddOverflow c)
    case pos =>
      rw [addNsw_saddOverflow_bitvec hbc]
      simp at hab
      simp [simp_iN, hab]
      /- a + b no overflow => (a + b) + c overflows -/
      /- ⊢ (a + b).saddOverflow c = true -/

      rw [BitVec.saddOverflow_comm]
      rw [BitVec.add_comm]
      /- ⊢ c.saddOverflow (b + a) = true -/

      /- hcb, hba (reverse them) -/
      rw [BitVec.saddOverflow_comm] at hbc
      rw [BitVec.saddOverflow_comm] at hab

      refine saddOverflow_pos_implies_sum ?_ hbc hab
      /- get hxyz in the right order -/
      ac_nf at *

    case neg =>
      /-
      case 2.
        hab : ¬a.saddOverflow b
        hbc : ¬b.saddOverflow c
      -/
      rw [addNsw_not_saddOverflow_bitvec_eq_add hab]
      rw [addNsw_not_saddOverflow_bitvec_eq_add hbc]

      simp [simp_iN]
      constructor
      . simp [BitVec.saddOverflow_assoc hab hbc]
      . intro h
        rw [← BitVec.saddOverflow_assoc hab hbc]
        simp [h]
        /- ⊢ a + (b + c) = a + b + c -/
        exact BitVec.add_assoc a b c

theorem addNsw_assoc_all_pos {n} {x y z : iN n}
    (hx : x ∈ i[0,∞])
    (hy : y ∈ i[0,∞])
    (hz : z ∈ i[0,∞])

    : (x +nsw y) +nsw z = x +nsw (y +nsw z) := by

  exact addNsw_assoc_same_sign (Or.inl ⟨hx, hy, hz⟩)

theorem addNsw_assoc_all_neg {n} {x y z : iN n}
    (hx : x ∈ i[-∞,0])
    (hy : y ∈ i[-∞,0])
    (hz : z ∈ i[-∞,0])

    : (x +nsw y) +nsw z = x +nsw (y +nsw z) := by

  exact addNsw_assoc_same_sign (Or.inr ⟨hx, hy, hz⟩)
