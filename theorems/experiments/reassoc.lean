import theorems.iN
import theorems.Opt
--import theorems.ideal.AC

def reassoc {idx} (ir : IR idx) : IR idx :=
  match ir with
  | .var _ | .const _ | .poison => ir

  /- con + x ~> x + con -/
  | .add (.const val) rhs  =>
    .add (reassoc rhs) (.const val)

  /- (con₁ + x) + con₂ ~> x + (con₁ + con₂) -/
  | .add (.add (.const con₁) x) (.const con₂) =>
    (IR.add (reassoc x) (.const (con₁ + con₂)))

  /- (con + x) + y ~> (x + y) + con) -/
  | .add (.add (.const con) x) y =>
    (IR.add (reassoc x) (reassoc y)).add (.const con)

  | .add (.var id1) (.var id2) =>
    if !(id1 < id2) then
      .add (.var id2) (.var id1)
    else
      ir

  | .add lhs rhs => .add (reassoc lhs) (reassoc rhs)
  | _ => ir

theorem eval_add_comm {idx} (ξ) (σ) (lhs rhs : IR idx)
  : IR.eval ξ σ (IR.add lhs rhs : IR idx) = IR.eval ξ σ (IR.add rhs lhs : IR idx) := by

  unfold IR.eval
  rw [add_comm]


/- bitvec (a + b) = bitvec a + bitvec b -/

theorem bitvec_add_eq_bitvec_add_bitvec {n}
  (a b : Nat)
  : @bitvec n ↑(a + b) = bitvec a + bitvec b := by

  simp [simp_iN, BitVec.ofNat_add]

def reassoc' : Rule :=
  { impl := reassoc

  , wf := by
      intros idx ξ σ lhs

      fun_induction reassoc <;> try rfl
      . rename_i ih
        unfold IR.eval

        orw [ih]
        rw [add_comm]
      . rename_i ih

        unfold IR.eval
        conv => lhs; lhs; unfold IR.eval
        conv => lhs; lhs; rw [add_comm]
        conv => lhs; rw [add_assoc]; rhs; unfold IR.eval;
        conv => rhs; rhs; unfold IR.eval

        orw [ih]
        rw [← bitvec_add_eq_bitvec_add_bitvec]
      . rename_i ihl ihr

        unfold IR.eval
        conv => lhs; lhs; unfold IR.eval
        conv => rhs; rhs; unfold IR.eval
        conv => rhs; lhs; unfold IR.eval
        conv => lhs; lhs; lhs; unfold IR.eval

        orw [ihl]
        orw [ihr]

        rw [add_assoc]
        rw [add_comm]

      . rw [eval_add_comm]
      . rename_i ihl ihr
        unfold IR.eval

        orw [ihl]
        orw [ihr]
  }

theorem example_comm {n} {x : iN n}
    : ((bitvec 4) + x) + x ~> (x + x) + (bitvec 4) := by

  opt reassoc'

theorem example_comm' {n} {x : iN n}
    : ((bitvec 4) + x) + (bitvec 5) ~> x + (bitvec 9) := by

  opt reassoc'
