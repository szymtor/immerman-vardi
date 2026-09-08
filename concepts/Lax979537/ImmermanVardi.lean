import Lax979537.FixedPointEvaluation

/-!
---
title: The Immerman–Vardi theorem
type: theorem
---
On finite linearly ordered relational structures, a query is definable in
first-order logic with least fixed points if and only if it is decidable
in deterministic polynomial time.

The vocabulary and query arity are arbitrary but fixed. The order is part
of the logical structure. Queries may depend on it; no order-independence
condition is imposed. The arity-zero instance is the usual statement for
Boolean properties of ordered structures.

The expressive direction is stated separately: every polynomial-time query
has an FO(LFP) definition. Its proof must represent polynomially bounded
Turing computations using tuples ordered lexicographically, and construct
the defining fixed-point formula. All such simulation work belongs to the
proof package, with no simulation premise added to the theorem.

References: Immerman, *Relational Queries Computable in Polynomial Time*
(1986), Theorem 2; Vardi, *The Complexity of Relational Query Languages*
(STOC 1982).
-/

namespace Lax979537.ImmermanVardi

open Lax979537.OrderedStructures Lax979537.FixedPointSemantics
open Lax979537.PolynomialTime

axiom ptimeDefinable {σ : Vocabulary} {k : Nat} (Q : Query σ k) :
    InP Q → Definable Q

axiom capturesPtime {σ : Vocabulary} {k : Nat} (Q : Query σ k) :
    Definable Q ↔ InP Q

end Lax979537.ImmermanVardi
