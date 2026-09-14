import Lax751879Proofs.FormulaDecision
import Lax751879.FixedPointEvaluation

namespace Lax751879Proofs.FixedPointEvaluation

open Lax751879.OrderedStructures Lax751879.FixedPointSyntax
open Lax751879.FixedPointSemantics Lax751879.PolynomialTime

/--
---
conclusion: Lax751879.FixedPointEvaluation.evaluationInP
---
The concrete finite TM2 decodes the input, evaluates the fixed formula by
materialized relation-table iteration, rejects malformed strings, and
returns one Boolean after clearing its workspace and resetting control.
-/
theorem evaluationInP {σ : Vocabulary} {k : Nat} (φ : Formula σ k) :
    InP (fun A => Satisfies A φ) :=
  ⟨DecisionProcedure.decideFormula φ, FormulaDecision.computableInPolyTime φ,
    DecisionProcedure.decideFormula_correct φ⟩

end Lax751879Proofs.FixedPointEvaluation
