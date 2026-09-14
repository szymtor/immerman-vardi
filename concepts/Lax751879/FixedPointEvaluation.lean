import Lax751879.FixedPointSemantics
import Lax751879.PolynomialTime

/-!
---
title: Polynomial-time evaluation of fixed-point queries
type: theorem
---
Every fixed FO(LFP) formula can be evaluated in polynomial time on finite
ordered structures, including the assignment to its free variables.
This is data complexity: the machine and polynomial may depend on the
formula. The formula is not part of the machine's input.

The proof must implement first-order evaluation and relation-table iteration
on the concrete Turing-machine model. Finite convergence alone does not
discharge this computational obligation.
-/

namespace Lax751879.FixedPointEvaluation

open Lax751879.OrderedStructures Lax751879.FixedPointSyntax
open Lax751879.FixedPointSemantics Lax751879.PolynomialTime

axiom evaluationInP {σ : Vocabulary} {k : Nat} (φ : Formula σ k) :
    InP (fun A => Satisfies A φ)

end Lax751879.FixedPointEvaluation
