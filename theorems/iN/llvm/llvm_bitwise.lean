import theorems.iN.SimpSets
import theorems.iN.iN_def

namespace iN

@[simp_iN]
def shl? {n} (a b : BitVec n) : iN n :=
  if n == 0 then
    0
  else if b >= n then
    poison
  else
    bitvec (a <<< b)

@[simp_iN]
def shl {n} (x y : iN n) : iN n := pBind₂ x y shl?

@[simp_iN]
def shlNsw? {n} (a b : BitVec n) : iN n :=
  if n == 0 then
    0
  else if ((a <<< b).sshiftRight' b ≠ a) then
    poison
  else
    shl? a b

@[simp_iN]
def shlNsw {n} (x y : iN n) : iN n := pBind₂ x y shlNsw?

@[simp_iN]
def shlNuw? {n} (a b : BitVec n) : iN n :=
  if n == 0 then
    0
  else if ((a <<< b) >>> b ≠ a) then
    poison
  else
    shl? a b

@[simp_iN]
def shlNuw {n} (x y : iN n) : iN n := pBind₂ x y shlNuw?

infixl:75 " << " => iN.shl
infixl:75 " <<nsw " => iN.shlNsw
infixl:75 " <<nuw " => iN.shlNuw

@[simp_iN]
def lshr? {n} (a b : BitVec n) : iN n :=
  if n == 0 then
    0
  else if b >= n then
    poison
  else
    bitvec (a >>> b)

@[simp_iN]
def lshr {n} (x y : iN n) : iN n := pBind₂ x y lshr?

@[simp_iN]
def lshrExact? {n} (a b : BitVec n) : iN n :=
  if n == 0 then
    0
  else if b >= n then
    poison
  else if (a <<< b) >>> b ≠ a then
    poison
  else
    lshr? a b

@[simp_iN]
def lshrExact {n} (x y : iN n) : iN n := pBind₂ x y lshrExact?

infixl:75 " >>ᵤ " => iN.lshr
infixl:75 " >>ᵤexact " => iN.lshrExact

@[simp_iN]
def ashr? {n} (a b : BitVec n) : iN n :=
  if n == 0 then
    0
  else if b >= n then
    poison
  else
    bitvec (a.sshiftRight' b)

@[simp_iN]
def ashr {n} (x y : iN n) : iN n := pBind₂ x y ashr?

@[simp_iN]
def ashrExact? {n} (a b : BitVec n) : iN n :=
  if n == 0 then
    0
  else if b >= n then
    poison
  else if (a >>> b) <<< b ≠ a then
    poison
  else
    ashr? a b

@[simp_iN]
def ashrExact {n} (x y : iN n) : iN n := pBind₂ x y ashrExact?

infixl:75 " >>ₛ " => iN.ashr
infixl:75 " >>ₛexact " => iN.ashrExact

@[simp_iN]
def and {n} (x y : iN n) : iN n := pBind₂ x y (fun a b => bitvec (a &&& b))

@[simp_iN]
def or {n} (x y : iN n) : iN n := pBind₂ x y (fun a b => bitvec (a ||| b))

@[simp_iN]
def not {n} (x : iN n) : iN n := pBind x (fun a => bitvec (~~~a))

@[simp_iN]
def xor {n} (x y : iN n) : iN n := pBind₂ x y (fun a b => bitvec (a ^^^ b))

/- we write ^' for XOR instead of ^ as that is taken by exponential.
  this might be a stupid decision, but can be changed later on
  - just find and replace "^'" -/

infixl:60 " & " => iN.and
infixl:55 " | " => iN.or
prefix:100 "~" => iN.not
infixl:58 " ^' " => iN.xor

end iN

section norm_eqs_simp_iN

@[simp_iN] theorem shl_eq_def : x << y = iN.shl x y := by rfl
@[simp_iN] theorem shlNsw_eq_def : x <<nsw y = iN.shlNsw x y := by rfl
@[simp_iN] theorem shlNuw_eq_def : x <<nuw y = iN.shlNuw x y := by rfl
@[simp_iN] theorem lshr_eq_def : x >>ᵤ y = iN.lshr x y := by rfl
@[simp_iN] theorem lshrExact_eq_def : x >>ᵤexact y = iN.lshrExact x y := by rfl
@[simp_iN] theorem ashr_eq_def : x >>ₛ y = iN.ashr x y := by rfl
@[simp_iN] theorem ashrExact_eq_def : x >>ₛexact y = iN.ashrExact x y := by rfl
@[simp_iN] theorem and_eq_def : x & y = iN.and x y := by rfl
@[simp_iN] theorem or_eq_def : x | y = iN.or x y := by rfl
@[simp_iN] theorem not_eq_def : ~x = iN.not x := by rfl
@[simp_iN] theorem xor_eq_def : x ^' y = iN.xor x y := by rfl

end norm_eqs_simp_iN
