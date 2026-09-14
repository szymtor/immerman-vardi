import Lax751879.ImmermanVardi
import Lax751879Proofs.FixedPointEvaluation
import Lax751879Proofs.AcceptanceCorrectness
import Lax751879Proofs.FiniteExceptions
import Lax751879Proofs.StructureEncoding

namespace Lax751879Proofs.ImmermanVardi

open Lax751879.OrderedStructures Lax751879.FixedPointSemantics
open Lax751879.PolynomialTime

/-- Transfer the evaluator's decision machine along the defining equivalence. -/
theorem definable_inP {σ : Vocabulary} {k : Nat} (Q : Query σ k)
    (hQ : Definable Q) : InP Q := by
  obtain ⟨φ, hφ⟩ := hQ
  obtain ⟨f, hf, hdec⟩ := Lax751879Proofs.FixedPointEvaluation.evaluationInP φ
  refine ⟨f, hf, fun w => (hdec w).trans ?_⟩
  exact exists_congr fun A => and_congr Iff.rfl (hφ A).symm

/--
---
conclusion: Lax751879.ImmermanVardi.ptimeDefinable
---
The concrete initialized rule LFP simulates the polynomial-time machine;
an accepting-output formula and finitely many small-domain cases define Q.
-/
theorem ptimeDefinable {σ : Vocabulary} {k : Nat} (Q : Query σ k) (hQ : InP Q) : Definable Q := by
  obtain ⟨f, ⟨h⟩, hf⟩ := hQ
  obtain ⟨d, hd⟩ := SimulationHorizon.exists_deciding_horizon h σ k
  let φ : Lax751879.FixedPointSyntax.Formula σ k :=
    ⟨AcceptanceFormula.formula h.tm h.inputAlphabet (h.outputAlphabet.symm true) σ k d,
      AcceptanceFormula.admissible h.tm h.inputAlphabet (h.outputAlphabet.symm true) σ k d⟩
  apply FiniteExceptions.definable_of_above Q (TraceCodes.threshold h.tm σ k) φ
  intro A hA
  have hn : TraceCodes.threshold h.tm σ k ≤ A.structureValue.size := Nat.le_of_lt hA
  have htwo : 2 ≤ A.structureValue.size := by unfold TraceCodes.threshold at hA; omega
  have heval : Satisfies A φ ↔ f (Lax751879.StructureEncoding.encode A) = true :=
    (AcceptanceCorrectness.eval_iff h d A hn (h.outputAlphabet.symm true)).trans ((hd A htwo true).trans eq_comm)
  rw [heval, hf]
  constructor
  · intro ha; exact ⟨A, rfl, ha⟩
  · rintro ⟨B, he, hb⟩
    have hBA := Lax751879Proofs.StructureEncoding.encodeInjective σ k he
    subst B
    exact hb

/--
---
conclusion: Lax751879.ImmermanVardi.capturesPtime
---
The concrete evaluator proves the computational direction. The initialized
positive-rule simulation and accepting-output formula prove the converse.
-/
theorem capturesPtime {σ : Vocabulary} {k : Nat} (Q : Query σ k) :
    Definable Q ↔ InP Q :=
  ⟨definable_inP Q, ptimeDefinable Q⟩

end Lax751879Proofs.ImmermanVardi
