import Lax751879Proofs.ImmermanVardi
import Mathlib.Data.Fin.VecNotation

open Turing Lax751879Proofs Lax751879.OrderedStructures Lax751879.FixedPointSemantics

namespace CapturesPtimeTest

@[reducible] def tm : FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ := fun _ => Bool
  Λ := Unit
  main := ()
  σ := Unit
  initialState := ()
  m := fun _ => .halt

-- Initial-node tags and parent positions remain distinct from time nodes.
example : InitialPatterns.node (w := 2) tm 1 (0 : Fin 3) 1 2 false ![0, 1] ![1, 0] =
    ![1, 1, 0, 1, 2, 1, 1, 0] := by decide
example : InitialPatterns.node (w := 2) tm 1 (0 : Fin 3) 1 2 true ![0, 1] ![1, 0] =
    ![1, 1, 0, 1, 2, 0, 0, 0] := by decide

@[reducible] def three : OrderedStructure [] := ⟨3, fun r => Fin.elim0 r⟩
example : eval (ClockLast.formula (σ := []) (ρ := []) (id : Fin 2 → Fin 2)) three
    (TupleCoding.clock (d := 2) (by decide : 0 < 3) 8) (fun i => Fin.elim0 i) := by
  rw [ClockLast.eval_formula]
  change (TupleAddresses.address 3 2 (TupleCoding.clock (by decide) 8)).val + 1 = 3 ^ 2
  rw [TupleCoding.clock_address]
  decide
example : ¬eval (ClockLast.formula (σ := []) (ρ := []) (id : Fin 2 → Fin 2)) three
    (TupleCoding.clock (d := 2) (by decide : 0 < 3) 7) (fun i => Fin.elim0 i) := by
  rw [ClockLast.eval_formula]
  change ¬(TupleAddresses.address 3 2 (TupleCoding.clock (by decide) 7)).val + 1 = 3 ^ 2
  rw [TupleCoding.clock_address]
  decide

-- The final theorem has no simulation premise, for any fixed vocabulary
-- and query arity, including Boolean properties and empty domains.
example {σ : Vocabulary} {k : Nat} (Q : Query σ k) :
    Definable Q ↔ Lax751879.PolynomialTime.InP Q := ImmermanVardi.capturesPtime Q

#print axioms InitialNodeSemantics.holds_last
#print axioms InitialNodeSemantics.holds_next
#print axioms InitialConfigSemantics.holds
#print axioms InitialSeeds.operator_iff
#print axioms CompiledRun.closure_eq_encoded
#print axioms CompiledRun.eval_membership
#print axioms RuleQuery.eval_formula
#print axioms AcceptanceFormula.admissible
#print axioms AcceptanceCorrectness.eval_iff
#print axioms ImmermanVardi.ptimeDefinable
#print axioms ImmermanVardi.capturesPtime

end CapturesPtimeTest
