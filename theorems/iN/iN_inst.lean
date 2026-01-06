import theorems.iN.llvm.llvm_binary
import theorems.iN.llvm.llvm_bitwise
import theorems.iN.llvm.llvm_cmp

/-
```
llvm_binary

  add             +
  addNsw          +nsw
  addNuw          +nuw
  addNw           +nw

  sub             -
  subNsw          -nsw
  subNuw          -nuw
  subNw           -nw

  mul             *
  mulNsw          *nsw
  mulNuw          *nuw
  mulNw           *nw

  sdiv            /ₛ
  udiv            /ᵤ
  udivExact       /ᵤexact

llvm_bitwise

  shl             <<
  shlNsw          <<nsw
  shlNuw          <<nuw
  shlNw           <<nw

  lshr            >>ᵤ
  lshrExact       >>ᵤexact
  ashr            >>ₛ
  ashrExact       >>ₛexact

  and             &&&
  or              |||
  not             ~~~
  xor             ^^^

llvm_cmp

  icmpEq          =='
  icmpNe          !='
  icmpUgt         >ᵤ
  icmpUge         ≥ᵤ
  icmpUlt         <ᵤ
  icmpUle         ≤ᵤ
  icmpSgt         >ₛ
  icmpSge         ≥ₛ
  icmpSlt         <ₛ
  icmpSle         ≤ₛ

```
-/
