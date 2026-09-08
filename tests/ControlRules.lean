import Lax979537Proofs.PlainClosure
import Lax979537Proofs.HeadPatterns

open Turing Lax979537Proofs Lax979537.OrderedStructures Lax979537.FixedPointSemantics

namespace ControlRulesTest

def tm : FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ := fun _ => Bool
  Λ := Unit
  main := ()
  σ := Bool
  initialState := false
  m := fun _ => .branch id .halt (.load (! ·) .halt)

def kind : TM2Micro.Cursor tm.Γ tm.Λ tm.σ → Nat
  | .instruction .halt => 0
  | .instruction (.load ..) => 1
  | .boundary none => 2
  | _ => 3

-- Distinct branch outcomes and the updated state are observable separately.
#guard (PlainControl.target tm (.instruction (tm.m ())) true).map (fun p => kind p.1) = some 0
#guard (PlainControl.target tm (.instruction (tm.m ())) false).map (fun p => kind p.1) = some 1
#guard (PlainControl.target tm (.instruction (.load (! ·) .halt)) false).map (fun p => (show Bool from p.2)) = some true
#guard (PlainControl.target tm (.instruction .halt) true).map (fun p => kind p.1) = some 2
#guard (PlainControl.target tm (.boundary none) true).map (fun p => (show Bool from p.2)) = some true
#guard (PlainControl.target tm (.instruction (.push () id .halt)) true).isNone

@[reducible] def three : OrderedStructure [] := ⟨3, fun r => Fin.elim0 r⟩

/-- The actual transition guard cannot wrap its final two-digit base-three
clock back to zero. -/
example : ¬eval
    (ControlRules.transition (σ := []) tm 0 2 0 (.boundary none) (.boundary none) false false).guard
    three (ControlRules.data Fin.elim0 (TupleCoding.clock (d := 2) (by decide : 0 < 3) 8)
      (TupleCoding.clock (d := 2) (by decide : 0 < 3) 0)
      (fun _ : Fin (ControlRules.headWidth tm 0) => (0 : Fin 3))) (fun i => Fin.elim0 i) := by
  dsimp only [ControlRules.transition]
  rw [AddressFormulas.eval_successor]
  simp only [ControlRules.data_before, ControlRules.data_after, TupleCoding.clock_address]
  decide

#print axioms ControlRules.transition_holds
#print axioms PlainControl.target_step
#print axioms PlainControl.operator_iff
#print axioms ControlValues.value_eq_configuration
#print axioms PlainClosure.preserves
#print axioms PlainClosure.derives
#print axioms HeadPatterns.map_update
#print axioms HeadPatterns.update_heads
#print axioms HeadPatterns.fresh_code

end ControlRulesTest
