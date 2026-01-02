import theorems.iN
import theorems.OptRw


theorem addNsw_refine_add {n} (x y : iN n)
    : x +nsw y ~> x + y := by

  poison_unroll x y => a b

  by_cases h : a.saddOverflow b
  . rw [addNsw_saddOverflow_bitvec h]
    exact Rewrite.poison_rewrite (bitvec a + bitvec b)
  . rw [addNsw_not_saddOverflow_bitvec_eq_add h]
    simp [simp_iN]

theorem add_assoc {n} {x y z : iN n}
    : (x + y) + z = x + (y + z) := by

  poison_unroll x y z => a b c
  simp [simp_iN, BitVec.add_assoc]

theorem add_comm {n} {x y : iN n}
    : x + y = y + x := by

  poison_unroll x y => a b
  simp [simp_iN, BitVec.add_comm]

theorem addNsw_assoc_add {n} {x y z : iN n}
    : x +nsw (y +nsw z) ~> (x + y) + z := by

  repeat opt_rw addNsw_refine_add
  rw [add_assoc]

theorem addNsw_comm {n} {x y : iN n}
    : x +nsw y = y +nsw x := by

  poison_unroll x y => a b
  simp_all [simp_iN, BitVec.saddOverflow_comm, BitVec.add_comm]
