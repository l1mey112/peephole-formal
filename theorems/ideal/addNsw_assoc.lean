import theorems.iN

structure Interval (bits : Nat) : Type where
  lo : BitVec bits /- signed -/
  hi : BitVec bits /- signed -/

def Interval.mem {n} (int : Interval n) : iN n → Prop
  | poison => True
  | bitvec a => int.lo.toInt ≤ a.toInt ∧ a.toInt ≤ int.hi.toInt

/- instance instMembe {n} : Membership (iN n) (Interval n) where
  mem := Interval.mem -/

/- TODO instance actually unwrapping to the thing fix  -/
notation:50 a:50 " ∈ " b:50 => Interval.mem b a

@[simp]
theorem Interval.bitvec_mem_ineq {n} (a : BitVec n) (int : Interval n)
    : bitvec a ∈ int ↔ int.lo.toInt ≤ a.toInt ∧ a.toInt ≤ int.hi.toInt := by

  constructor
  . intro h
    unfold Interval.mem at h
    simp [h]
  . intro h
    unfold Interval.mem
    simp [h]

/- decide p || decide q ↔ p ∨ q -/

@[simp]
theorem toInt_le_intMax {n} (a : BitVec n)
  : a.toInt ≤ 2 ^ (n - 1) - 1 := by

  /- a.toInt ≤ BitVec.intMax -/

  /- split
  rename_i h -/
  sorry

@[simp]
theorem addNsw_saddOverflow_bitvec {n} {a b : BitVec n} (h : a.saddOverflow b)
    : (bitvec a) +nsw (bitvec b) = poison := by

  simp [simp_iN, h]

@[simp]
theorem addNsw_not_saddOverflow_bitvec_eq_add {n} {a b : BitVec n} (h : ¬a.saddOverflow b)
    : (bitvec a) +nsw (bitvec b) = bitvec (a + b) := by

  simp [simp_iN, h]

theorem saddOverflow_iff_or {n} (x y : BitVec n)
    : x.saddOverflow y
      ↔ x.toInt + y.toInt ≥ 2 ^ (n - 1) ∨ x.toInt + y.toInt < - 2 ^ (n - 1) := by

  unfold BitVec.saddOverflow
  rw [← Bool.decide_or]
  rw [decide_eq_true_eq]

theorem saddOverflow_pos_implies_sum {n} {a b c : BitVec n}
  (hx : 0 ≤ a.toInt) (hy : 0 ≤ b.toInt) (hz : 0 ≤ c.toInt)
  (hab : a.saddOverflow b)
  (hbc : ¬b.saddOverflow c)
  : a.saddOverflow (b + c) := by

  /- (b + c).toInt ≥ b.toInt -/

  have h : (b + c).toInt ≥ b.toInt := by
    rw [BitVec.toInt_add_of_not_saddOverflow hbc]
    omega

  rw [saddOverflow_iff_or]
  left

  rw [saddOverflow_iff_or] at hab
  /- want to combine hab with h -/
  obtain habl | habr := hab
  <;> omega

theorem BitVec.saddOverflow_comm {n} {a b : BitVec n}
    : a.saddOverflow b = b.saddOverflow a := by

  grind [BitVec.saddOverflow]

theorem bool_eq_false_iff_not {b : Bool}
    : b = false ↔ ¬b := by

  simp

theorem addNsw_assoc_all_pos {n} (x y z : iN n)
    (hx : x ∈ (⟨0, BitVec.intMax n⟩ : Interval n))
    (hy : y ∈ (⟨0, BitVec.intMax n⟩ : Interval n))
    (hz : z ∈ (⟨0, BitVec.intMax n⟩ : Interval n))

    : (x +nsw y) +nsw z <~> x +nsw (y +nsw z) := by

  cases x
  case poison => simp [simp_iN]
  case bitvec a =>
  cases y
  case poison => simp [simp_iN]
  case bitvec b =>
  cases z
  case poison => simp [simp_iN]
  case bitvec c =>

  simp_all

  /- case 1. (a + b) + c overflow ↔ a + (b + c) overflow -/
  /- case 2. none of them overflow -/

  by_cases hab : (a.saddOverflow b)
  case pos =>
    rw [addNsw_saddOverflow_bitvec hab]
    simp [simp_iN]
    /- b + c no overflow => a + (b + c) overflows -/
    intro hbc

    rw [bool_eq_false_iff_not] at hbc
    exact saddOverflow_pos_implies_sum hx hy hz hab hbc

  case neg =>
    by_cases hbc : (b.saddOverflow c)
    case pos =>
      rw [addNsw_saddOverflow_bitvec hbc]
      simp [simp_iN]

      /- a + b no overflow => (a + b) + c overflows -/
      intro hab
      rw [bool_eq_false_iff_not] at hab
      rw [BitVec.saddOverflow_comm]
      rw [BitVec.add_comm]

      /- ⊢ c.saddOverflow (b + a) = true -/

      rw [BitVec.saddOverflow_comm] at hbc
      rw [BitVec.saddOverflow_comm] at hab
      /- hcb, hba (reverse them) -/

      exact saddOverflow_pos_implies_sum hz hy hx hbc hab

    case neg =>

      /-
      case 2.
        hab : ¬a.saddOverflow b
        hbc : ¬b.saddOverflow c
      -/
      rw [addNsw_not_saddOverflow_bitvec_eq_add hab]
      rw [addNsw_not_saddOverflow_bitvec_eq_add hbc]

      simp [simp_iN] /- TODO incredibly brittle -/
      constructor
      . /- a.saddOverflow (b + c) = true → (a + b).saddOverflow c = true -/
        simp [BitVec.saddOverflow_assoc hab hbc]

      . intro h
        simp [BitVec.saddOverflow_assoc hab hbc]

        constructor
        . exact h

        intro _
        exact (Eq.symm $ BitVec.add_assoc a b c)
