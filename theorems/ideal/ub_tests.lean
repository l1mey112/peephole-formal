import theorems.iN

/-


∀ (x : iN n), f x ~> g x → ∀ (x y : BitVec n), f x = g x


(well formedness)
- f x != poison for x != poison
- g x != poison for x != poison

  => f, g doesn't introduce MORE UB

---------------------------------------------

(UB equivalent)
- f x = poison ↔ g x = poison


 -/


/-


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

/- (huge + small) + (-small)

  huge + (small + (-small)) -/

theorem addNsw_assoc_same_sign (x y z : iN 32)
    (h :
      (x ≥ₛ 0) &&& (y ≥ₛ 0) &&& (z ≥ₛ 0) ~> 1 ∨
      (x <ₛ 0) &&& (y <ₛ 0) &&& (z <ₛ 0) ~> 1)

    : (x +nsw y) +nsw z <~> x +nsw (y +nsw z) := by

  iN_convert_goal_bitvec
  simp [simp_iN]

  intro h
  bv_decide

/-
def BitVec.slt := 2 -/


/-
(h :
  (x ≥ₛ 0) &&& (y ≥ₛ 0) &&& (z ≥ₛ 0) ~> 1 ∨
  (x <ₛ 0) &&& (y <ₛ 0) &&& (z <ₛ 0) ~> 1)
-/
def hyp {n} (a b c : BitVec n) :=
  !(a.sle 0) && !(b.sle 0) && !(c.sle 0) ∨
  (a.slt 0) && (b.slt 0) && (c.slt 0)


/- theorem add_zero {n} (x : iN n) : x + 0 ~> x := by
  iN_convert_goal_bitvec
  simp [simp_iN]
 -/
