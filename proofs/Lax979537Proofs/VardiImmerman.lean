import Lax979537.VardiImmerman
import Lax979537Proofs.FixedPointEvaluation

namespace Lax979537Proofs.VardiImmerman

open Lax979537.OrderedStructures Lax979537.FixedPointSemantics
open Lax979537.PolynomialTime

/-- Transfer the evaluator's decision machine along the defining equivalence. -/
theorem definable_inP {σ : Vocabulary} {k : Nat} (Q : Query σ k)
    (hQ : Definable Q) : InP Q := by
  obtain ⟨φ, hφ⟩ := hQ
  obtain ⟨f, hf, hdec⟩ := Lax979537Proofs.FixedPointEvaluation.evaluationInP φ
  refine ⟨f, hf, fun w => (hdec w).trans ?_⟩
  exact exists_congr fun A => and_congr Iff.rfl (hφ A).symm

/--
---
conclusion: Lax979537.VardiImmerman.capturesPtime
assumptions:
  - Lax979537.VardiImmerman.ptimeDefinable
---
The forward direction uses the proved concrete evaluator. The theorem
remains conditional on the reverse machine-to-formula simulation.
-/
theorem capturesPtime {σ : Vocabulary} {k : Nat} (Q : Query σ k) :
    Definable Q ↔ InP Q :=
  ⟨definable_inP Q, Lax979537.VardiImmerman.ptimeDefinable Q⟩

end Lax979537Proofs.VardiImmerman
