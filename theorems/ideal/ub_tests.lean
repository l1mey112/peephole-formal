import theorems.iN

/-

theorem addNsw_assoc_same_sign {n} (x y z : iN n)
    (h :
      (x ≥ₛ 0) &&& (y ≥ₛ 0) &&& (z ≥ₛ 0) ~> 1 ∨
      (x <ₛ 0) &&& (y <ₛ 0) &&& (z <ₛ 0) ~> 1)

    : (x +nsw y) +nsw z <~> x +nsw (y +nsw z) := by

  sorry


theorem addNsw_assoc_all_pos {n} (x y z : iN n)
    (hx : x ∈ [0,-])
    (hy : y ∈ [0,-])
    (hz : z ∈ [0,-])

    : (x +nsw y) +nsw z <~> x +nsw (y +nsw z) := by

  sorry

f x

f poison = poison

f(x) = 1

f(poison) = 1

 -/

--theorem t (f : iN n → iN n) (noub : noUb f) : (∀ (x : BitVec n), f x = x) → ∀ (x : iN n), f x ~> x :=

-- (wf : f poison = poison)

def noUb (f : iN n → iN n) :=
  ∀x : iN n, f x = poison ↔ x = poison

def wF {n} (f : iN n → iN n) := f poison = poison

-- noUb → wF
-- noUb f ∧ noUb g → ubEquiv'
-- noUb f ∧ noUb g → ubEquiv

-- wF f ∧ wF g → ubEquiv'

/-
-/

def ubEquiv' {n} (f : iN n → iN n) (g : iN n → iN n) :=
  f poison = g poison

def ubEquiv {n} (f : iN n → iN n) (g : iN n → iN n) :=
  ∀ x : iN n, f x = poison ↔ g x = poison


-- (∀ (x : iN n), f x ~> g x) → ∀ (x : BitVec n), f x = g x

-- ∀ (x : iN n), f x ~> g x → f x = g x

theorem t (f : iN n → iN n) (g : iN n → iN n) (ub : ubEquiv f g)
  (x : iN n) : f x ~> g x → f x = g x := by

  intro as

  cases h1 : (f x)
  case bitvec a =>
    rw [h1] at as
    rw [Rewrite.rewrite_bitvec_iN a (g x)] at as
    rw [as]
  case poison =>
    rw [(ub x).mp]
    exact h1

theorem t₁ (f : iN n → iN n) (g : iN n → iN n) (ub : ubEquiv f g)
  : (∀ (x : iN n), f x ~> g x)
    → ∀ (x : iN n), f x = g x := by

  intro h
  intro x
  have h1 := h x

  cases h2 : (f x)
  case bitvec a =>
    rw [h2] at h1
    rw [Rewrite.rewrite_bitvec_iN a (g x)] at h1
    rw [h1]
  case poison =>
    rw [(ub x).mp]
    exact h2

/--
We have that f x ~> g x implies f (bitvec a) = f (bitvec a) if we know
that f produces UB exactly when g produces UB.
-/
theorem tt₁ (f : iN n → iN n) (g : iN n → iN n)
  (ub : ubEquiv f g)
  : (∀x : iN n, f x ~> g x)
    → ∀a : BitVec n, f (bitvec a) = g (bitvec a) := by

  intro h
  have h1 := (t₁ f g ub) h
  intro a
  exact h1 (bitvec a)

/--
We have that f (bitvec a) = f (bitvec a) implies f x ~> g x if we know
that when f = g when both take in UB.
-/
theorem tt₂ (f : iN n → iN n) (g : iN n → iN n)
  (wf : ubEquiv' f g)
  : (∀a : BitVec n, f (bitvec a) = g (bitvec a))
    → ∀x : iN n, f x ~> g x := by

  intro as
  intro x

  cases h1 : (f x)
  case bitvec a =>
    rw [Rewrite.rewrite_bitvec_iN]
    rw [← h1]

    cases x
    case bitvec b =>
      exact (Eq.symm $ as b)
    case poison =>
      exact (Eq.symm wf)
  case poison => simp

/- theorem tt₂ (f : iN n → iN n) (g : iN n → iN n)
  (wf : ubEquiv' f g)
  : (∀a : BitVec n, f (bitvec a) ~> g (bitvec a))
    → ∀x : iN n, f x ~> g x := by

  /- exact (tt₁ f g wf) -/

  intro h
  have h1 := (tt f g wf) h


  sorry

theorem tt₁_test {n} (x y : iN n)
  : x + y ~> y + x := by

  apply tt₁
  case a =>
    intro a
    revert x

    apply tt₁
 -/
