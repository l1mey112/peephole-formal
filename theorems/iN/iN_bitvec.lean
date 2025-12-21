import theorems.iN.iN_def
import theorems.iN.iN_llvm

/-- `poison_unroll x y z => a b c`

Performs `cases x; cases y; cases z`, solves every `poison` branch with
`simp [simp_iN]`, and in the unique `bitvec` branch introduces the
variables named `a b c`. -/
syntax "poison_unroll" (ppSpace colGt ident)* " =>" (ppSpace colGt ident)* : tactic
macro_rules
| `(tactic| poison_unroll $xs:ident* => $ys:ident*) =>
  `(tactic|
    ($[cases $xs:ident with
      | bitvec $ys:ident => ?_
      | poison => simp [simp_iN]];*);

      try simp at * /- simp hypotheses with bitvec -/
    )

theorem BitVec.saddOverflow_comm {n} {a b : BitVec n}
    : a.saddOverflow b = b.saddOverflow a := by

  grind [BitVec.saddOverflow]

theorem BitVec.uaddOverflow_comm {n} {a b : BitVec n}
    : a.uaddOverflow b = b.uaddOverflow a := by

  grind [BitVec.uaddOverflow]

theorem saddOverflow_iff_or_unfold {n} (x y : BitVec n)
    : x.saddOverflow y
      ↔ x.toInt + y.toInt ≥ 2 ^ (n - 1) ∨ x.toInt + y.toInt < - 2 ^ (n - 1) := by

  unfold BitVec.saddOverflow
  rw [← Bool.decide_or]
  exact decide_eq_true_iff

theorem uaddOverflow_iff_unfold {n} (x y : BitVec n)
    : x.uaddOverflow y
      ↔ x.toNat + y.toNat ≥ 2 ^ n := by

  unfold BitVec.uaddOverflow
  exact decide_eq_true_iff

@[simp]
theorem saddOverflow_zero {n} (x : BitVec n)
    : x.saddOverflow 0#n = false := by

  unfold BitVec.saddOverflow
  rw [← Bool.decide_or, decide_eq_false]
  simp
  constructor
  . exact BitVec.toInt_lt
  . exact BitVec.le_toInt x

@[simp]
theorem uaddOverflow_zero {n} (x : BitVec n)
    : x.uaddOverflow 0#n = false := by

  unfold BitVec.uaddOverflow
  rw [decide_eq_false]
  simp
  exact BitVec.isLt x

@[simp]
theorem ssubOverflow_zero {n} (x : BitVec n)
    : x.ssubOverflow 0#n = false := by

  unfold BitVec.ssubOverflow
  rw [decide_eq_false]
  simp
  . exact BitVec.le_toInt x
  . simp; exact BitVec.toInt_lt

@[simp]
theorem usubOverflow_zero {n} (x : BitVec n)
    : x.usubOverflow 0#n = false := by

  unfold BitVec.usubOverflow
  rw [decide_eq_false]
  simp

theorem addNsw_saddOverflow_bitvec {n} {a b : BitVec n} (h : a.saddOverflow b)
    : (bitvec a) +nsw (bitvec b) = poison := by

  simp [simp_iN, h]

theorem addNsw_not_saddOverflow_bitvec_eq_add {n} {a b : BitVec n} (h : ¬a.saddOverflow b)
    : (bitvec a) +nsw (bitvec b) = bitvec (a + b) := by

  simp [simp_iN, h]

theorem addNuw_uaddOverflow_bitvec {n} {a b : BitVec n} (h : a.uaddOverflow b)
    : (bitvec a) +nuw (bitvec b) = poison := by

  simp [simp_iN, h]

theorem addNuw_not_uaddOverflow_bitvec_eq_add {n} {a b : BitVec n} (h : ¬a.uaddOverflow b)
    : (bitvec a) +nuw (bitvec b) = bitvec (a + b) := by

  simp [simp_iN, h]
