import theorems.iN.iN_def

/--
`Rewrite x y` means the value `x` can be rewritten into the value `y`.

Rewriting both ways, i.e., `Rewrite x y ∧ Rewrite y x`, means `x = y`.
This is a theorem, proved by `Rewrite.rewriteIff_iff_eq`.
-/
inductive Rewrite {n} : iN n → iN n → Prop where
  /-- A value rewrites to itself. -/
  | refl (x : iN n) : Rewrite x x
  /-- Poison can be rewritten into any concrete value. -/
  | poison_forge (v : BitVec n) : Rewrite poison (bitvec v)

@[inherit_doc] infix:50 " ~> "  => Rewrite

namespace Rewrite

attribute [refl] Rewrite.refl

/-- Poison can be rewritten to anything. -/
@[simp, grind .]
theorem poison_rewrite {n} (x : iN n)
    : poison ~> x := by

  cases x
  case bitvec a =>
    exact Rewrite.poison_forge a
  case poison =>
    rfl

/--
`rewrite_trivial` tries to solve goal of the form `x ~> x` or `poison ~> x`.
-/
syntax "rewite_trivial" : tactic

macro_rules | `(tactic| trivial) => `(tactic| apply Rewrite.poison_rewrite)

macro_rules | `(tactic| rewite_trivial) => `(tactic| try (with_reducible rfl))
macro_rules | `(tactic| rewite_trivial) => `(tactic| apply Rewrite.poison_rewrite)

/-- Values cannot be rewritten to poison. -/
@[simp, grind! .]
theorem not_bitvec_poision_rewrite {n} (a : BitVec n)
    : ¬bitvec a ~> poison := by

  intro h
  cases h

@[simp, grind =]
theorem rewrite_poison_eq_poison {n} {x : iN n}
    : (x ~> poison) ↔ (x = poison) := by

  constructor
  case mp =>
    intro h
    cases h
    case refl => rfl
  case mpr =>
    intro h
    rw [h]

instance {n} : @Std.Refl (iN n) Rewrite where
  refl := Rewrite.refl

@[grind →]
theorem trans {n} {x y z : iN n}
    (hx : x ~> y) (hy : y ~> z) : x ~> z := by

  cases hx
  case refl =>
    exact hy
  case poison_forge v =>
    exact poison_rewrite z

instance {n} : Trans (@Rewrite n) (@Rewrite n) (@Rewrite n) where
  trans := trans

/--
Rewrite congruence. Even though no instruction should be able to
"observe" poison, `wf` must still be an assumption.
-/
theorem congrApp {n m} (f : iN n → iN m)
    (wf : f poison = poison)
    {a a' : iN n} (h : a ~> a') : f a ~> f a' := by

  cases h
  case refl =>
    rfl
  case poison_forge v =>
    rw [wf]
    exact poison_rewrite (f (bitvec v))

@[grind .]
theorem eq_implies_rewrite {n} (x y : iN n)
    : (x = y) → x ~> y := by

  intro h
  rw [h]

@[simp, grind =]
theorem rewrite_bitvec_bitvec {n} (a b : BitVec n)
    : (bitvec a ~> bitvec b) ↔ a = b := by

  constructor
  case mp =>
    intro h
    cases h
    case refl => rfl
  case mpr =>
    intro h
    rw [h]

@[simp, grind =]
theorem rewrite_bitvec_iN {n} (a : BitVec n) (y : iN n)
    : (bitvec a ~> y) ↔ y = bitvec a := by

  constructor
  case mp =>
    intro h
    cases h
    case refl => rfl
  case mpr =>
    intro h
    rw [h]

@[simp, grind =]
theorem rewrite_iff_poison {n} (x : iN n)
    : (x ~> poison) ↔ (x = poison) := by

  constructor
  case mp =>
    intro h
    cases h
    simp_all
  case mpr =>
    intro h
    rw [h]

@[simp]
theorem bitvec_rewrite_poison_iff {n} (a : BitVec n)
    : (bitvec a ~> poison) ↔ False := by

  constructor
  case mp =>
    intro h
    cases h
  case mpr =>
    intro h
    cases h

@[simp]
theorem rewriteIff_iff_eq {n} {a b : iN n}
    : (a ~> b ∧ b ~> a) ↔ (a = b) := by

  constructor
  case mp =>
    intro h
    cases h with
    | intro hab hba =>
      cases hab
      cases hba
      rfl
      simp_all

  case mpr =>
    intro h
    rw [h]
    constructor <;> rfl

@[simp, grind →]
theorem rewrite_forward_back_implies_eq {n} {a b : iN n}
    (h₁ : a ~> b) (h₂ : b ~> a)
    : a = b := by

  exact rewriteIff_iff_eq.mp ⟨h₁, h₂⟩

instance {n} : @Std.Antisymm (iN n) (@Rewrite n) where
  antisymm := @rewrite_forward_back_implies_eq n

@[simp]
theorem if_then_poison_rewrite_iff {n} (c : Prop) [Decidable c] (x y : iN n)
    : (if c then poison else x : no_index _) ~> y ↔ ¬c → x ~> y := by

  split <;> simp [*]

@[simp]
theorem bitvec_rewrite_if_then_poison_iff {n} (a : BitVec n) (c : Prop) [Decidable c] (y : iN n)
    : bitvec a ~> (if c then poison else y : no_index _) ↔ ¬c ∧ bitvec a ~> y := by

  split <;> simp [*]

@[simp]
theorem if_then_rewrite_if_then_iff {n} (c : Prop) [Decidable c] (x1 x2 y1 y2 : iN n)
    : (if c then x1 else x2 : no_index _) ~> (if c then y1 else y2 : no_index _) ↔
      (c → x1 ~> y1) ∧ (¬c → x2 ~> y2) := by

  split <;> simp [*]

@[simp]
theorem if_then_rewrite_iff {n} (c : Prop) [Decidable c] (x1 x2 y : iN n)
    : (if c then x1 else x2 : no_index _) ~> y ↔
      (c → x1 ~> y) ∧ (¬c → x2 ~> y) := by

  split <;> simp [*]

@[simp]
theorem rewrite_if_then_iff {n} (c : Prop) [Decidable c] (x : iN n) (y1 y2 : iN n)
    : x ~> (if c then y1 else y2 : no_index _) ↔
      (c → x ~> y1) ∧ (¬c → x ~> y2) := by

  split <;> simp [*]

@[simp]
theorem bitvec_rewrite_iff_if_then_poison_iff {n} (a : BitVec n) (c : Prop) [Decidable c] (y : iN n)
    : bitvec a = (if c then poison else y : no_index _) ↔ ¬c ∧ bitvec a ~> y := by

  split <;> grind

@[simp]
theorem if_then_rewrite_iff_if_then_iff {n} (c : Prop) [Decidable c] (x1 x2 y1 y2 : iN n)
    : (if c then x1 else x2 : no_index _) = (if c then y1 else y2 : no_index _) ↔
      (c → x1 = y1) ∧ (¬c → x2 = y2) := by

  split <;> grind

@[simp]
theorem if_then_rewrite_iff_iff {n} (c : Prop) [Decidable c] (x1 x2 y : iN n)
    : (if c then x1 else x2 : no_index _) = y ↔
      (c → x1 = y) ∧ (¬c → x2 = y) := by

  split <;> grind

@[simp]
theorem rewrite_iff_if_then_iff {n} (c : Prop) [Decidable c] (x : iN n) (y1 y2 : iN n)
    : x = (if c then y1 else y2 : no_index _) ↔
      (c → x = y1) ∧ (¬c → x = y2) := by

  split <;> grind

end Rewrite

namespace iN

@[simp]
theorem pBind₂_pBind_left {n m k l} (x : iN n) (y : iN k)
    (f : BitVec n → iN m) (g : BitVec m → BitVec k → iN l) :
    pBind₂ (pBind x f) y g = pBind x (fun a => pBind₂ (f a) y g) := by

  unfold pBind₂; grind

@[simp]
theorem pBind₂_pBind_right {n m k l} (x : iN n) (y : iN m)
    (f : BitVec m → iN k) (g : BitVec n → BitVec k → iN l) :
    pBind₂ x (pBind y f) g = pBind₂ x y (fun a b => pBind (f b) (fun c => g a c)) := by

  unfold pBind₂; grind

@[simp]
theorem pBind_pBind₂_assoc {n m k l} (x : iN n) (y : iN m)
    (f : BitVec n → BitVec m → iN k) (g : BitVec k → iN l) :
    pBind (pBind₂ x y f) g = pBind₂ x y (fun a b => pBind (f a b) g) := by

  unfold pBind₂; grind

@[simp]
theorem pBind_ite {n m} (c : Prop) [Decidable c] (x y : iN n) (f : BitVec n → iN m) :
    pBind (if c then x else y) f = if c then pBind x f else pBind y f := by
  split <;> rfl

@[simp]
theorem pBind_cond {n m} (c : Bool) (x y : iN n) (f : BitVec n → iN m) :
    pBind (cond c x y) f = cond c (pBind x f) (pBind y f) := by
  cases c <;> rfl

@[simp]
theorem pBind₂_ite_left {n m k} (c : Prop) [Decidable c] (x1 x2 : iN n) (y : iN m)
    (f : BitVec n → BitVec m → iN k) :
    pBind₂ (if c then x1 else x2) y f = if c then pBind₂ x1 y f else pBind₂ x2 y f := by
  split <;> rfl

@[simp]
theorem pBind₂_ite_right {n m k} (c : Prop) [Decidable c] (x : iN n) (y1 y2 : iN m)
    (f : BitVec n → BitVec m → iN k) :
    pBind₂ x (if c then y1 else y2) f = if c then pBind₂ x y1 f else pBind₂ x y2 f := by
  split <;> simp

@[simp]
theorem pBind₂_cond_left {n m k} (c : Bool) (x1 x2 : iN n) (y : iN m)
    (f : BitVec n → BitVec m → iN k) :
    pBind₂ (cond c x1 x2) y f = cond c (pBind₂ x1 y f) (pBind₂ x2 y f) := by
  cases c <;> rfl

@[simp]
theorem pBind₂_cond_right {n m k} (c : Bool) (x : iN n) (y1 y2 : iN m)
    (f : BitVec n → BitVec m → iN k) :
    pBind₂ x (cond c y1 y2) f = cond c (pBind₂ x y1 f) (pBind₂ x y2 f) := by
  cases c <;> simp

@[simp, grind .]
theorem pBind_const_bitvec {n m} (x : iN n) (v : BitVec m) :
    pBind x (fun _ => bitvec v) = if x = poison then poison else bitvec v := by

  unfold pBind; grind

end iN


namespace iN

@[simp]
theorem pBind_rewrite_left {n m} (x : iN n) (f : BitVec n → iN m) (z : iN m) :
    (pBind x f ~> z) ↔ match x with
      | bitvec a => f a ~> z
      | poison => True := by
  cases x <;> simp

@[simp]
theorem rewrite_pBind_right {n m} (z : iN n) (x : iN m) (f : BitVec m → iN n) :
    (z ~> pBind x f) ↔ match x with
      | bitvec a => z ~> f a
      | poison => z = poison := by
  cases x <;> simp

@[simp high, grind]
theorem pBind_rewrite_pBind_same {n m} (x : iN n) (f g : BitVec n → iN m) :
    (pBind x f ~> pBind x g) ↔ match x with
      | bitvec a => f a ~> g a
      | poison => True := by
  cases x <;> simp

@[simp]
theorem pBind₂_rewrite_left {n m k} (x : iN n) (y : iN m) (f : BitVec n → BitVec m → iN k) (z : iN k) :
    (pBind₂ x y f ~> z) ↔ match x, y with
      | bitvec a, bitvec b => f a b ~> z
      | _, _ => True := by
  cases x <;> cases y <;> simp

@[simp]
theorem rewrite_pBind₂_right {n m k} (z : iN k) (x : iN n) (y : iN m) (f : BitVec n → BitVec m → iN k) :
    (z ~> pBind₂ x y f) ↔ match x, y with
      | bitvec a, bitvec b => z ~> f a b
      | _, _ => z = poison := by
  cases x <;> cases y <;> simp

@[simp high, grind]
theorem pBind₂_rewrite_pBind₂_same {n m k} (x : iN n) (y : iN m) (f g : BitVec n → BitVec m → iN k) :
    (pBind₂ x y f ~> pBind₂ x y g) ↔ match x, y with
      | bitvec a, bitvec b => f a b ~> g a b
      | _, _ => True := by
  cases x <;> cases y <;> simp

end iN
