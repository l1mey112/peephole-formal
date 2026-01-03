import theorems.iN.SimpSets
import theorems.iN.iN_def

namespace iN

@[simp_iN]
def icmpEq? {n} (x y : BitVec n) : iN 1 := ⟦bif x == y then 1 else 0⟧

@[simp_iN]
def icmpEq {n} (x y : iN n) : iN 1 := pBind₂ x y icmpEq?

@[simp_iN]
def icmpNe? {n} (x y : BitVec n) : iN 1 := bitvec (bif x != y then 1 else 0)

@[simp_iN]
def icmpNe {n} (x y : iN n) : iN 1 := pBind₂ x y icmpNe?

@[simp_iN]
def icmpUgt? {n} (x y : BitVec n) : iN 1 := bitvec (bif x > y then 1 else 0)

@[simp_iN]
def icmpUgt {n} (x y : iN n) : iN 1 := pBind₂ x y icmpUgt?

@[simp_iN]
def icmpUge? {n} (x y : BitVec n) : iN 1 := bitvec (bif x >= y then 1 else 0)

@[simp_iN]
def icmpUge {n} (x y : iN n) : iN 1 := pBind₂ x y icmpUge?

@[simp_iN]
def icmpUlt? {n} (x y : BitVec n) : iN 1 := bitvec (bif x < y then 1 else 0)

@[simp_iN]
def icmpUlt {n} (x y : iN n) : iN 1 := pBind₂ x y icmpUlt?

@[simp_iN]
def icmpUle? {n} (x y : BitVec n) : iN 1 := bitvec (bif x <= y then 1 else 0)

@[simp_iN]
def icmpUle {n} (x y : iN n) : iN 1 := pBind₂ x y icmpUle?

@[simp_iN]
def icmpSgt? {n} (x y : BitVec n) : iN 1 := bitvec (bif x.sle y then 0 else 1) -- inverse

@[simp_iN]
def icmpSgt {n} (x y : iN n) : iN 1 := pBind₂ x y icmpSgt?

@[simp_iN]
def icmpSge? {n} (x y : BitVec n) : iN 1 := bitvec (bif x.slt y then 0 else 1) -- inverse

@[simp_iN]
def icmpSge {n} (x y : iN n) : iN 1 := pBind₂ x y icmpSge?

@[simp_iN]
def icmpSlt? {n} (x y : BitVec n) : iN 1 := bitvec (bif x.slt y then 1 else 0)

@[simp_iN]
def icmpSlt {n} (x y : iN n) : iN 1 := pBind₂ x y icmpSlt?

@[simp_iN]
def icmpSle? {n} (x y : BitVec n) : iN 1 := bitvec (bif x.sle y then 1 else 0)

@[simp_iN]
def icmpSle {n} (x y : iN n) : iN 1 := pBind₂ x y icmpSle?

/-
we want to define equality as == but that conflicts with BEq.
note that BEq (==) is NOT icmpEq (==') as it does not consider poison values
-/

infixl:55 " ==' " => iN.icmpEq
infixl:55 " !=' " => iN.icmpNe
infixl:55 " >ᵤ "  => iN.icmpUgt
infixl:55 " ≥ᵤ "  => iN.icmpUge
infixl:55 " <ᵤ "  => iN.icmpUlt
infixl:55 " ≤ᵤ "  => iN.icmpUle
infixl:55 " >ₛ "  => iN.icmpSgt
infixl:55 " ≥ₛ "  => iN.icmpSge
infixl:55 " <ₛ "  => iN.icmpSlt
infixl:55 " ≤ₛ "  => iN.icmpSle

end iN

section norm_eqs_simp_iN

@[simp_iN] theorem icmpEq_eq_def : (x ==' y) = iN.icmpEq x y := by rfl
@[simp_iN] theorem icmpNe_eq_def : (x !=' y) = iN.icmpNe x y := by rfl
@[simp_iN] theorem icmpUgt_eq_def : x >ᵤ y = iN.icmpUgt x y := by rfl
@[simp_iN] theorem icmpUge_eq_def : x ≥ᵤ y = iN.icmpUge x y := by rfl
@[simp_iN] theorem icmpUlt_eq_def : x <ᵤ y = iN.icmpUlt x y := by rfl
@[simp_iN] theorem icmpUle_eq_def : x ≤ᵤ y = iN.icmpUle x y := by rfl
@[simp_iN] theorem icmpSgt_eq_def : x >ₛ y = iN.icmpSgt x y := by rfl
@[simp_iN] theorem icmpSge_eq_def : x ≥ₛ y = iN.icmpSge x y := by rfl
@[simp_iN] theorem icmpSlt_eq_def : x <ₛ y = iN.icmpSlt x y := by rfl
@[simp_iN] theorem icmpSle_eq_def : x ≤ₛ y = iN.icmpSle x y := by rfl

end norm_eqs_simp_iN
