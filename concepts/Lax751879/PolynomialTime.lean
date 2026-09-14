import Lax751879.StructureEncoding
import Mathlib.Computability.TuringMachine.Computable

/-!
---
title: Polynomial-time queries on ordered structures
type: definition
---
A query is polynomial-time decidable when a finite deterministic Turing
machine decides the language of encodings of its satisfying pointed
structures within a polynomial in the input bit length. Malformed encodings
are rejected. The machine and polynomial are fixed for the query.

The machine model and step count are mathlib's bundled finite multi-stack
Turing machines (`TM2ComputableInPolyTime`), with identity encoding on input
bit strings and a single output bit. This is the same underlying complexity
notion used in Lax51, specialized directly to bit-string decision problems.
There is no abstract computation oracle or machine-simulation hypothesis.
-/

namespace Lax751879.PolynomialTime

open Lax751879.OrderedStructures Lax751879.StructureEncoding

def language {σ : Vocabulary} {k : Nat} (Q : Query σ k) (w : List Bool) : Prop :=
  ∃ A : PointedStructure σ k, encode A = w ∧ Q A

def InP {σ : Vocabulary} {k : Nat} (Q : Query σ k) : Prop :=
  ∃ f : List Bool → Bool,
    Nonempty (Turing.TM2ComputableInPolyTime id (fun b => [b]) f) ∧
    ∀ w, f w = true ↔ language Q w

end Lax751879.PolynomialTime
