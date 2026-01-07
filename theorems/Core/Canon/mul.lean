import theorems.iN


/- def Pow2 {n} : iN n → Prop
  | poison => True
  | bitvec a => ∃k ≤ n, a = BitVec.twoPow n k -/ /- a.toNat.isPowerOfTwo -/

/- TODO see basic_bitwise.lean -/

/- def CPow2 {n} (c : BitVec n) : Prop := c.toNat.isPowerOfTwo

/- TODO create log2 for BitVec -/

theorem test {n} (x : iN n) (c : Fin n)
    : x << ⟦c⟧ = x * ⟦BitVec.twoPow n c⟧ := by

  poison_unroll x => a


  sorry

theorem mul_pow2_rewrite_shift {n} (x : iN n) (c : BitVec n)
    (h : CPow2 c)
    : x * ⟦c⟧ = x << ⟦Nat.log2 c.toNat⟧ := by



  sorry -/
