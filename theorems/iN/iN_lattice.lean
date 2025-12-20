import theorems.iN.iN_def

structure Interval (bits : Nat) : Type where
  lo : BitVec bits := BitVec.intMin bits
  hi : BitVec bits := BitVec.intMax bits

def Interval.mem {n} (int : Interval n) : iN n → Prop
  | poison => True
  | bitvec a => int.lo.toInt ≤ a.toInt ∧ a.toInt ≤ int.hi.toInt

/- instance instMembe {n} : Membership (iN n) (Interval n) where
  mem := Interval.mem -/

/- TODO instance actually unwrapping to the thing fix  -/
notation:50 a:50 " ∈ " b:50 => Interval.mem b a

syntax:100 "i[" term ",∞]" : term
syntax:100 "i[-∞," term "]" : term
syntax:100 "i[" term "," term "]" : term

macro_rules
  | `(i[$a:term,∞]) => `({ lo := $a : Interval _})
  | `(i[-∞,$b:term]) => `({ hi := $b : Interval _})
  | `(i[$a:term,$b:term]) => `({ lo := $a, hi := $b : Interval _})

@[simp]
theorem Interval.bitvec_mem_lo_iff_ineq {n} (a : BitVec n) (lo : BitVec n)
    : bitvec a ∈ { lo := lo : Interval n} ↔ lo.toInt ≤ a.toInt := by

  simp [Interval.mem, BitVec.toInt_le]

@[simp]
theorem Interval.bitvec_mem_hi_iff_ineq {n} (a : BitVec n) (hi : BitVec n)
    : bitvec a ∈ { hi := hi : Interval n} ↔ a.toInt ≤ hi.toInt := by

  by_cases h : (0 < n)
  case pos =>
    simp [Interval.mem, BitVec.toInt_intMin_of_pos h, BitVec.le_toInt]

  case neg =>

    have h' : n = 0 := by omega
    subst h'
    grind [Interval.mem]
