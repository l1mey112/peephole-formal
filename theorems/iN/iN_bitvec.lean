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


/- theorem BitVec.smulOverflow_one'0 (x : BitVec 0)
    : x.smulOverflow 0 = false := by bv_decide

theorem BitVec.smulOverflow_one'1 (x : BitVec 1)
    : x.smulOverflow 1#1 = false := by bv_decide

theorem BitVec.smulOverflow_one'2 (x : BitVec 2)
    : x.smulOverflow 1#2 = false := by bv_decide

theorem BitVec.smulOverflow_one'16 (x : BitVec 16)
    : x.smulOverflow 1#16 = false := by bv_decide

theorem BitVec.smulOverflow_one'32 (x : BitVec 32)
    : x.smulOverflow 1#32 = false := by bv_decide -/

/- @[simp]
theorem BitVec.smulOverflow_one {n} (x : BitVec n)
    : x.smulOverflow 1#n = false := by

  unfold BitVec.smulOverflow
  by_cases h : n = 0
  . subst h; simp

  by_cases h : n = 1
  . subst h; simp;
    by_cases h : x = 0#1
    . subst h; simp;
    . have h2 : x = 1#1 := by
        bv_omega

      subst h2

  have : x.toInt * (1#n).toInt = x.toInt := by

    rw [BitVec.toInt_one]

    exact Int.mul_one x.toInt

    simp [h]


  --simp only [Bool.false_or, decide_eq_false_iff_not, Int.not_lt]



  simp [] -/
