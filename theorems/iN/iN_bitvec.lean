import theorems.iN.iN_def
import theorems.iN.iN_inst

theorem BitVec.saddOverflow_comm {n} {a b : BitVec n}
    : a.saddOverflow b = b.saddOverflow a := by

  grind [BitVec.saddOverflow]

theorem BitVec.uaddOverflow_comm {n} {a b : BitVec n}
    : a.uaddOverflow b = b.uaddOverflow a := by

  grind [BitVec.uaddOverflow]

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
