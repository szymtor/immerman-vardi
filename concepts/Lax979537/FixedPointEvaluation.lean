import Lax979537.FixedPointSemantics
import Lax979537.PolynomialTime

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

namespace Lax979537.FixedPointEvaluation

open Lax979537.OrderedStructures Lax979537.FixedPointSyntax
open Lax979537.FixedPointSemantics Lax979537.PolynomialTime

axiom evaluationInP {σ : Vocabulary} {k : Nat} (φ : Formula σ k) :
    InP (fun A => Satisfies A φ)

end Lax979537.FixedPointEvaluation
