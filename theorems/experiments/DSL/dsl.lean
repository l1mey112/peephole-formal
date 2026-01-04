import theorems.iN
import theorems.OptRw

/- instance instanceSingleton {n} : Singleton (BitVec n) (iN n) where
  singleton := bitvec

attribute [simp] instanceSingleton

 -/

theorem const_sdiv_const_rewrite_const'8 (a b : BitVec 8)

    : ⟦a⟧ /ₛ ⟦b⟧ ~> ⟦a.sdiv b⟧ := by

  simp [simp_iN]

theorem add'8 (a b : BitVec 8)

    : ⟦a⟧ + ⟦b⟧ = ⟦a + b⟧ := by

  simp [simp_iN]

def Pow2 {n} : iN n → Prop
  | poison => True
  | bitvec a => ∃k ≤ n, a = BitVec.twoPow n k /- a.toNat.isPowerOfTwo -/

namespace iN

infixl:60 " & " => iN.and

end iN

theorem urem_zero {n} (x : iN n)
    : x %ᵤ ⟦0⟧ ~> poison := by

  simp [simp_iN]

theorem mod_eq_and_sub_one'8 (x y : iN 8)
    (h : Pow2 y)

    : x %ᵤ y ~> x & (y - (bitvec 1)) := by

  poison_unroll x y => a b

  by_cases hz : b = 0
  case pos =>
    rw [hz]
    orw [urem_zero]

  sorry

/-
  unfold Pow2 at h
  simp at *

  rcases h with ⟨k, hk⟩
  rw [hk]

  unfold BitVec.twoPow at *
  /-
  case bitvec.bitvec
  a b : BitVec 8
  k : Nat
  hk : b = 1#8 <<< k
  ⊢ ¬1#8 <<< k = 0#8 → a &&& 1#8 <<< k - 1#8 = a % 1#8 <<< k
  -/

  have h : ¬1#8 <<< k = 0#8 := by
    bv_decide

  bv_decide

  /- ⊢ x.pBind₂ y iN.urem? ~> x.pBind₂ (y.pBind fun a => bitvec (a - 1#8)) fun a b => bitvec (a &&& b) -/

  sorry -/
