import theorems.iN

/- # x + 0 -/

theorem add_zero {n} (x : iN n) : x + 0 = x := by
  cases x
  all_goals simp [simp_iN]

theorem addNsw_zero {n} (x : iN n) : x +nsw 0 = x := by
  cases x
  all_goals simp [simp_iN]

theorem addNuw_zero {n} (x : iN n) : x +nuw 0 = x := by
  cases x
  all_goals simp [simp_iN]

theorem addNw_zero {n} (x : iN n) : x +nw 0 = x := by
  cases x
  all_goals simp [simp_iN]

/- # x - 0 -/

theorem sub_zero {n} (x : iN n) : x - 0 = x := by
  cases x
  all_goals simp [simp_iN]

theorem subNsw_zero {n} (x : iN n) : x -nsw 0 = x := by
  cases x
  all_goals simp [simp_iN]

theorem subNuw_zero {n} (x : iN n) : x -nuw 0 = x := by
  cases x
  all_goals simp [simp_iN]

theorem subNw_zero {n} (x : iN n) : x -nw 0 = x := by
  cases x
  all_goals simp [simp_iN]
