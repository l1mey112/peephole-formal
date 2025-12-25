import theorems.iN
import Lean

theorem addNsw_refine_add {n} (x y : iN n)
    : x +nsw y ~> x + y := by

  poison_unroll x y => a b

  by_cases h : a.saddOverflow b
  . rw [addNsw_saddOverflow_bitvec h]
    exact Rewrite.poison_rewrite (bitvec a + bitvec b)
  . rw [addNsw_not_saddOverflow_bitvec_eq_add h]
    simp [simp_iN]

theorem add_assoc {n} {x y z : iN n}
    : (x + y) + z = x + (y + z) := by

  poison_unroll x y z => a b c
  simp [simp_iN, BitVec.add_assoc]

theorem add_comm {n} {x y : iN n}
    : x + y = y + x := by

  poison_unroll x y => a b
  simp [simp_iN, BitVec.add_comm]

theorem addNsw_assoc_add {n} {x y z : iN n}
    : x +nsw (y +nsw z) ~> (x + y) + z := by

  repeat opt_rw addNsw_refine_add
  rw [add_assoc]

/- -------------- -/

theorem addNsw_comm {n} {x y : iN n}
    : x +nsw y = y +nsw x := by

  poison_unroll x y => a b
  simp_all [simp_iN, BitVec.saddOverflow_comm, BitVec.add_comm]

instance {n} : @Std.Associative (iN n) iN.add where
  assoc := @add_assoc n

instance {n} : @Std.Commutative (iN n) iN.add where
  comm := @add_comm n

instance {n} : @Std.Commutative (iN n) iN.addNsw where
  comm := @addNsw_comm n

theorem test {n} (a b c : iN n) : a + (b + c) = (a +nsw b) +nsw c := by

  ac_nf0


  sorry

open Lean Elab Tactic Meta

#check iN.bitvec

/- inductive iNExpr where
| add : iNExpr → iNExpr → iNExpr
| addNsw : iNExpr → iNExpr → iNExpr -/

/- partial def iNExpr_wf (validNames : Std.HashSet Name) (e : Expr) : MetaM Unit := do
  if e.isFVar then
    return ()

  match_expr e with
  | Rewrite _ lhs rhs => do
    iNExpr_wf validNames lhs; iNExpr_wf validNames rhs
    return ()
  | Eq lhs rhs => do
    iNExpr_wf validNames lhs; iNExpr_wf validNames rhs
    return ()
  | _ => pure ()

  match_expr e with
  | bitvec _ _ => return ()
  | poison _ => return ()
  | _ => pure ()

  if let some _ := (← getOfNatValue? e ``iN) then
    return ()

  match e.getAppFn with
  | Expr.const c _ => do
    if validNames.contains c then
      for ex in e.getAppArgs[1:] do
        iNExpr_wf validNames ex
      return ()
  | _ => pure ()

  throwError m!"Invalid iN expression: {e}"

elab "tactic_test" : tactic => withMainContext do
  let e ← getMainTarget

  /- instDefinitions.getTheorems -/
  let instructions := validInstructions.getState (← getEnv)
  let validNames := Std.HashSet.ofList instructions

  iNExpr_wf validNames e


#check List _ → Std.HashSet _

theorem example_reassoc {n} {x : iN n}
    : (bitvec 4) +nsw (x +nsw bitvec 5) ~> x + bitvec 9 := by


  tactic_test

  /- simp [addNsw_refine_add]

 -/
  /- opt_rw addNsw_assoc_add
  rw [@add_comm n (bitvec 4) x]
  rw [add_assoc]
  simp -/

  sorry -/
