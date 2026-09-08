import Lax979537Proofs.FormulaDecision
import Lax979537.FixedPointEvaluation

namespace Lax979537Proofs.FixedPointEvaluation

open Lax979537.OrderedStructures Lax979537.FixedPointSyntax
open Lax979537.FixedPointSemantics Lax979537.PolynomialTime

/--
---
conclusion: Lax979537.FixedPointEvaluation.evaluationInP
---
The concrete finite TM2 decodes the input, evaluates the fixed formula by
materialized relation-table iteration, rejects malformed strings, and
returns one Boolean after clearing its workspace and resetting control.
-/
theorem evaluationInP {σ : Vocabulary} {k : Nat} (φ : Formula σ k) :
    InP (fun A => Satisfies A φ) :=
  ⟨DecisionProcedure.decideFormula φ, FormulaDecision.computableInPolyTime φ,
    DecisionProcedure.decideFormula_correct φ⟩

end Lax979537Proofs.FixedPointEvaluation
