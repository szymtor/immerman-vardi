import Lax751879Proofs.HeadPatterns
import Lax751879Proofs.PushEffects

namespace Lax751879Proofs.PushPatterns

open Turing FactPatterns HeadPatterns RuleConstants ControlRules

variable {tm : FinTM2} {n N m d w : Nat}

/-- A push has two positive conclusions: its immutable node record and
its successor configuration. Both use the source clock as the fresh key. -/
noncomputable def output (tm : FinTM2) (zero one two control state symbol : Fin N)
    (key : tm.K) (emit : Bool) (x y : Fin d → Fin N)
    (h : Fin (headWidth tm w) → Fin N) : Fin (FactCodes.payloadWidth tm d w + 1) → Fin N :=
  if emit then record tm d zero one (fresh zero two x) symbol (get tm h key)
  else configuration tm zero zero y control state (HeadPatterns.update tm h key (fresh zero two x))

theorem map_output (tm : FinTM2) (f : Fin N → Fin n) (zero one two control state symbol : Fin N)
    (key : tm.K) (emit : Bool) (x y : Fin d → Fin N) (h : Fin (headWidth tm w) → Fin N) :
    f ∘ output tm zero one two control state symbol key emit x y h =
      output tm (f zero) (f one) (f two) (f control) (f state) (f symbol) key emit
        (f ∘ x) (f ∘ y) (f ∘ h) := by
  cases emit <;> simp only [output, Bool.false_eq_true, ↓reduceIte,
    map_record, map_configuration, map_fresh, map_get, map_update]

noncomputable def value (hn : MachineConstants.bound tm ≤ n) (e : PushEffects.Effect tm)
    (v : tm.σ) (emit : Bool) (x y : Fin d → Fin n) (h : Fin (headWidth tm w) → Fin n) :
    Fin (FactCodes.payloadWidth tm d w + 1) → Fin n :=
  output tm ⟨0, by have := MachineConstants.enough tm; omega⟩
    ⟨1, by have := MachineConstants.enough tm; omega⟩ ⟨2, by have := MachineConstants.enough tm; omega⟩
    (SupportedCodes.code _ ((MachineConstants.controls_bound tm).trans hn) e.next)
    (@TupleCoding.finiteCode tm.σ tm.σFin n ((MachineConstants.states_bound tm).trans hn) v)
    (SupportedCodes.code _ ((MachineConstants.symbols_bound tm).trans hn) (Sigma.mk e.key e.symbol))
    e.key emit x y h

noncomputable def pattern (tm : FinTM2) (m d w : Nat) (e : PushEffects.Effect tm)
    (v : tm.σ) (emit : Bool) :
    Fin (FactCodes.payloadWidth tm d w + 1) → Fin (MachineConstants.bound tm + numVars tm m d w) :=
  output tm (Fin.castAdd _ (MachineConstants.numeral tm 0))
    (Fin.castAdd _ (MachineConstants.numeral tm 1)) (Fin.castAdd _ (MachineConstants.numeral tm 2))
    (Fin.castAdd _ (MachineConstants.control tm e.next)) (Fin.castAdd _ (MachineConstants.state tm v))
    (Fin.castAdd _ (MachineConstants.symbol tm (Sigma.mk e.key e.symbol))) e.key emit
    (Fin.natAdd _ ∘ before m d (headWidth tm w)) (Fin.natAdd _ ∘ after m d (headWidth tm w))
    (Fin.natAdd _ ∘ ControlRules.heads m d (headWidth tm w))

theorem assignment_pattern (hn : MachineConstants.bound tm ≤ n)
    (a : Fin (numVars tm m d w) → Fin n) (e : PushEffects.Effect tm) (v : tm.σ) (emit : Bool) :
    assignment hn a ∘ pattern tm m d w e v emit = value hn e v emit
      (a ∘ before m d (headWidth tm w)) (a ∘ after m d (headWidth tm w))
      (a ∘ ControlRules.heads m d (headWidth tm w)) := by
  rw [pattern, map_output]
  have hd {k : Nat} (z : Fin k → Fin (numVars tm m d w)) :
      assignment hn a ∘ (Fin.natAdd _ ∘ z) = a ∘ z := by funext i; simp [assignment]
  rw [hd, hd, hd]
  simp only [assignment, Fin.append_left]
  rfl

end Lax751879Proofs.PushPatterns
