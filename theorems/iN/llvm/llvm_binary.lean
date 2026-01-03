import theorems.iN.SimpSets
import theorems.iN.iN_def
import theorems.iN.iN_rewrite

namespace iN

@[simp_iN]
def add? {n} (a b : BitVec n) : iN n := bitvec (a + b)

@[simp_iN]
def add {n} (x y : iN n) : iN n := pBind₂ x y add?

@[simp_iN]
def addNsw? {n} (a b : BitVec n) : iN n :=
  if BitVec.saddOverflow a b then
    poison
  else
    add? a b

@[simp_iN]
def addNsw {n} (x y : iN n) : iN n := pBind₂ x y addNsw?

@[simp_iN]
def addNuw? {n} (a b : BitVec n) : iN n :=
  if BitVec.uaddOverflow a b then
    poison
  else
    add? a b

@[simp_iN]
def addNuw {n} (x y : iN n) : iN n := pBind₂ x y addNuw?

@[simp_iN]
def addNw? {n} (a b : BitVec n) : iN n :=
  if BitVec.saddOverflow a b then
    poison
  else if BitVec.uaddOverflow a b then
    poison
  else
    add? a b

@[simp_iN]
def addNw {n} (x y : iN n) : iN n := pBind₂ x y addNw?

@[simp_iN]
instance : Add (iN n) where
  add := iN.add

infixl:65 " +nsw " => iN.addNsw
infixl:65 " +nuw " => iN.addNuw
infixl:65 " +nw "  => iN.addNw

@[simp_iN]
def sub? {n} (a b : BitVec n) : iN n := bitvec (a - b)

@[simp_iN]
def sub {n} (x y : iN n) : iN n := pBind₂ x y sub?

@[simp_iN]
def subNsw? {n} (a b : BitVec n) : iN n :=
  if BitVec.ssubOverflow a b then
    poison
  else
    sub? a b

@[simp_iN]
def subNsw {n} (x y : iN n) : iN n := pBind₂ x y subNsw?

@[simp_iN]
def subNuw? {n} (a b : BitVec n) : iN n :=
  if BitVec.usubOverflow a b then
    poison
  else
    sub? a b

@[simp_iN]
def subNuw {n} (x y : iN n) : iN n := pBind₂ x y subNuw?

@[simp_iN]
def subNw? {n} (a b : BitVec n) : iN n :=
  if BitVec.ssubOverflow a b then
    poison
  else if BitVec.usubOverflow a b then
    poison
  else
    sub? a b

@[simp_iN]
def subNw {n} (x y : iN n) : iN n := pBind₂ x y subNw?

@[simp_iN]
instance : Sub (iN n) where
  sub := iN.sub

infixl:65 " -nsw " => iN.subNsw
infixl:65 " -nuw " => iN.subNuw
infixl:65 " -nw "  => iN.subNw

@[simp_iN]
def mul? {n} (a b : BitVec n) : iN n := bitvec (a * b)

@[simp_iN]
def mul {n} (x y : iN n) : iN n := pBind₂ x y mul?

@[simp_iN]
def mulNsw? {n} (a b : BitVec n) : iN n :=
  if BitVec.smulOverflow a b then
    poison
  else
    mul? a b

@[simp_iN]
def mulNsw {n} (x y : iN n) : iN n := pBind₂ x y mulNsw?

@[simp_iN]
def mulNuw? {n} (a b : BitVec n) : iN n :=
  if BitVec.umulOverflow a b then
    poison
  else
    mul? a b

@[simp_iN]
def mulNuw {n} (x y : iN n) : iN n := pBind₂ x y mulNuw?

@[simp_iN]
def mulNw? {n} (a b : BitVec n) : iN n :=
  if BitVec.smulOverflow a b then
    poison
  else if BitVec.umulOverflow a b then
    poison
  else
    mul? a b

@[simp_iN]
def mulNw {n} (x y : iN n) : iN n := pBind₂ x y mulNw?

@[simp_iN]
instance : Mul (iN n) where
  mul := iN.mul

infixl:65 " *nsw " => iN.mulNsw
infixl:65 " *nuw " => iN.mulNuw
infixl:65 " *nw "  => iN.mulNw

@[simp_iN]
def sdiv? {n} (a b : BitVec n) : iN n :=
  if b == 0 then
    poison
  else if b == -1 && a == BitVec.intMin n then
    poison
  else
    bitvec (a.sdiv b)

@[simp_iN]
def sdiv {n} (x y : iN n) : iN n := pBind₂ x y sdiv?

@[simp_iN]
def udiv? {n} (a b : BitVec n) : iN n :=
  if b == 0 then
    poison
  else
    bitvec (a.udiv b)

@[simp_iN]
def udiv {n} (x y : iN n) : iN n := pBind₂ x y udiv?

@[simp_iN]
def udivExact? {n} (a b : BitVec n) : iN n :=
  if b == 0 then
    poison
  else if a.umod b != 0 then
    poison
  else
    bitvec (a.udiv b)

@[simp_iN]
def udivExact {n} (x y : iN n) : iN n := pBind₂ x y udivExact?

infixl:70 " /ₛ " => iN.sdiv
infixl:70 " /ᵤ " => iN.udiv
infixl:70 " /ᵤexact " => iN.udivExact

@[simp_iN]
def srem? {n} (a b : BitVec n) : iN n :=
  if b == 0 then
    poison
  else if b == -1 && a == BitVec.intMin n then
    poison
  else
    bitvec (a.smod b)

@[simp_iN]
def srem {n} (x y : iN n) : iN n := pBind₂ x y srem?

@[simp_iN]
def urem? {n} (a b : BitVec n) : iN n :=
  if b == 0 then
    poison
  else
    bitvec (a.umod b)

@[simp_iN]
def urem {n} (x y : iN n) : iN n := pBind₂ x y urem?

infixl:70 " %ₛ " => iN.srem
infixl:70 " %ᵤ " => iN.urem

end iN

section norm_eqs_simp_iN

@[simp_iN] theorem add_eq_def : x + y = iN.add x y := rfl
@[simp_iN] theorem addNsw_eq_def : x +nsw y = iN.addNsw x y := rfl
@[simp_iN] theorem addNuw_eq_def : x +nuw y = iN.addNuw x y := rfl
@[simp_iN] theorem addNw_eq_def  : x +nw  y = iN.addNw  x y := rfl
@[simp_iN] theorem sub_eq_def : x - y = iN.sub x y := rfl
@[simp_iN] theorem subNsw_eq_def : x -nsw y = iN.subNsw x y := rfl
@[simp_iN] theorem subNuw_eq_def : x -nuw y = iN.subNuw x y := rfl
@[simp_iN] theorem subNw_eq_def  : x -nw  y = iN.subNw  x y := rfl
@[simp_iN] theorem mul_eq_def : x * y = iN.mul x y := rfl
@[simp_iN] theorem mulNsw_eq_def : x *nsw y = iN.mulNsw x y := rfl
@[simp_iN] theorem mulNuw_eq_def : x *nuw y = iN.mulNuw x y := rfl
@[simp_iN] theorem mulNw_eq_def  : x *nw  y = iN.mulNw  x y := rfl
@[simp_iN] theorem sdiv_eq_def : x /ₛ y = iN.sdiv x y := rfl
@[simp_iN] theorem udiv_eq_def : x /ᵤ y = iN.udiv x y := rfl
@[simp_iN] theorem udivExact_eq_def : x /ᵤexact y = iN.udivExact x y := rfl
@[simp_iN] theorem srem_eq_def : x %ₛ y = iN.srem x y := rfl
@[simp_iN] theorem urem_eq_def : x %ᵤ y = iN.urem x y := rfl

end norm_eqs_simp_iN
