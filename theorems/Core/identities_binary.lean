import theorems.iN

/- # Add -/

theorem add_zero (x : iN n) : x + 0 = x := by
  poison_unroll' x

theorem addNsw_zero (x : iN n) : x +nsw 0 = x := by
  poison_unroll' x

theorem addNuw_zero (x : iN n) : x +nuw 0 = x := by
  poison_unroll' x

theorem addNw_zero (x : iN n) : x +nw 0 = x := by
  poison_unroll' x

/- # Sub -/

theorem sub_zero (x : iN n) : x - 0 = x := by
  poison_unroll' x

theorem subNsw_zero (x : iN n) : x -nsw 0 = x := by
  poison_unroll' x

theorem subNuw_zero (x : iN n) : x -nuw 0 = x := by
  poison_unroll' x

theorem subNw_zero (x : iN n) : x -nw 0 = x := by
  poison_unroll' x

theorem sub_self (x : iN n) : x - x ~> 0 := by
  poison_unroll' x

theorem subNsw_self (x : iN n) : x -nsw x ~> 0 := by
  poison_unroll' x

theorem subNuw_self (x : iN n) : x -nuw x ~> 0 := by
  poison_unroll' x

theorem subNw_self (x : iN n) : x -nw x ~> 0 := by
  poison_unroll' x

/- # Mul -/

theorem mul_zero (x : iN n) : x * 0 ~> 0 := by
  poison_unroll' x

theorem mulNsw_zero (x : iN n) : x *nsw 0 ~> 0 := by
  poison_unroll' x

theorem mulNuw_zero (x : iN n) : x *nuw 0 ~> 0 := by
  poison_unroll' x

theorem mulNw_zero (x : iN n) : x *nw 0 ~> 0 := by
  poison_unroll' x

theorem mul_one (x : iN n) : x * 1 = x := by
  poison_unroll' x

theorem mulNsw_one (hn : n ≥ 2) (x : iN n) : x *nsw 1 = x := by
  poison_unroll x => a; simp [simp_iN, hn]

theorem mulNuw_one (x : iN n) : x *nuw 1 = x := by
  poison_unroll' x

theorem mulNw_one (hn : n ≥ 2) (x : iN n) : x *nw 1 = x := by
  poison_unroll x => a; simp [simp_iN, hn]

/- # Div -/

theorem sdiv_one (hn : n ≥ 2) (x : iN n) : x /ₛ 1 = x := by
  poison_unroll x => a

  have h : 1#n = -1#n → False := by
    intro h
    have := BitVec.one_eq_neg_one h
    omega

  simp [simp_iN]
  constructor
  . exact Nat.ne_zero_of_lt hn
  . intros; contradiction

theorem udiv_one (hn : n ≥ 1) (x : iN n) : x /ᵤ 1 = x := by
  poison_unroll x => a; simp [simp_iN, Nat.ne_zero_of_lt hn]

theorem sdiv_self (hn : n ≥ 1) (x : iN n) (h : x ≠ 0) : x /ₛ x ~> 1 := by
  poison_unroll x => a; simp [simp_iN]
  have : ¬n = 0 := Nat.ne_zero_of_lt hn
  try grind

theorem udiv_self (hn : n ≥ 1) (x : iN n) (h : x ≠ 0) : x /ᵤ x ~> 1 := by
  poison_unroll x => a; simp [simp_iN]
  have : ¬n = 0 := Nat.ne_zero_of_lt hn
  try grind
