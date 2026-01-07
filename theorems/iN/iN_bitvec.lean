import theorems.iN.iN_def
import theorems.iN.iN_inst

theorem BitVec.saddOverflow_comm {n} {a b : BitVec n}
    : a.saddOverflow b = b.saddOverflow a := by

  grind [BitVec.saddOverflow]

theorem BitVec.uaddOverflow_comm {n} {a b : BitVec n}
    : a.uaddOverflow b = b.uaddOverflow a := by

  grind [BitVec.uaddOverflow]

theorem BitVec.smulOverflow_comm {n} {a b : BitVec n}
    : a.smulOverflow b = b.smulOverflow a := by

  grind [BitVec.smulOverflow]

theorem BitVec.umulOverflow_comm {n} {a b : BitVec n}
    : a.umulOverflow b = b.umulOverflow a := by

  grind [BitVec.umulOverflow]

theorem BitVec.saddOverflow_iff_or_unfold {n} (x y : BitVec n)
    : x.saddOverflow y
      ↔ x.toInt + y.toInt ≥ 2 ^ (n - 1) ∨ x.toInt + y.toInt < - 2 ^ (n - 1) := by

  unfold BitVec.saddOverflow
  rw [← Bool.decide_or]
  exact decide_eq_true_iff

theorem BitVec.uaddOverflow_iff_unfold {n} (x y : BitVec n)
    : x.uaddOverflow y
      ↔ x.toNat + y.toNat ≥ 2 ^ n := by

  unfold BitVec.uaddOverflow
  exact decide_eq_true_iff

@[simp]
theorem BitVec.saddOverflow_zero {n} (x : BitVec n)
    : x.saddOverflow 0#n = false := by

  unfold BitVec.saddOverflow
  rw [← Bool.decide_or, decide_eq_false]
  simp
  constructor
  . exact BitVec.toInt_lt
  . exact BitVec.le_toInt x

@[simp]
theorem BitVec.uaddOverflow_zero {n} (x : BitVec n)
    : x.uaddOverflow 0#n = false := by

  unfold BitVec.uaddOverflow
  rw [decide_eq_false]
  simp
  exact BitVec.isLt x

@[simp]
theorem BitVec.ssubOverflow_zero {n} (x : BitVec n)
    : x.ssubOverflow 0#n = false := by

  unfold BitVec.ssubOverflow
  rw [decide_eq_false]
  simp
  . exact BitVec.le_toInt x
  . simp; exact BitVec.toInt_lt

@[simp]
theorem BitVec.usubOverflow_zero {n} (x : BitVec n)
    : x.usubOverflow 0#n = false := by

  unfold BitVec.usubOverflow
  rw [decide_eq_false]
  simp

attribute [simp] BitVec.toInt_lt BitVec.le_toInt BitVec.isLt

@[simp]
theorem BitVec.smulOverflow_one {n} (hn : n ≥ 2) (x : BitVec n)
    : x.smulOverflow 1#n = false := by

  have h : x.toInt * (1#n).toInt = x.toInt := by
    rw [BitVec.toInt_one (show 1 < n by exact Nat.lt_of_succ_le hn)]
    exact Int.mul_one x.toInt

  simp [BitVec.smulOverflow, h]

@[simp]
theorem BitVec.umulOverflow_one {n} (x : BitVec n)
    : x.umulOverflow 1#n = false := by

  simp [BitVec.umulOverflow]
  by_cases hn : n = 0
  . subst hn; simp

  have h: 1 % 2 ^ n = 1 := by
    exact Nat.one_mod_two_pow_eq_one.mpr (show n > 0 from Nat.pos_of_ne_zero hn)

  simp [h]

theorem BitVec.one_eq_neg_one {n}
    (h : 1#n = -1#n)
    : n = 0 ∨ n = 1 := by

  by_cases hb : n = 0 ∨ n = 1
  . assumption

  have hb : ¬n = 0 ∧ ¬n = 1 := by simp_all

  have : (1#n).msb = (-1#n).msb := by
    rw [← h]

  /- 1#n is not zero or intMin -/
  have neqIntMin : 1#n ≠ BitVec.intMin n := by grind
  have neqZero : 1#n ≠ 0#n := by grind

  /- hence we can show that their msb's are different -/
  have m1 : (1#n).msb = false := by simp [BitVec.msb, hb]; omega
  have m2 : (-1#n).msb = true := by
    rw [BitVec.msb_neg_of_ne_intMin_of_ne_zero neqIntMin neqZero]
    simp [hb]

  rw [m1, m2] at this
  contradiction

@[simp]
theorem bitvec_of_length_zero (a : BitVec 0) : ⟦a⟧ = ⟦0⟧ := by
  simp [BitVec.of_length_zero]
