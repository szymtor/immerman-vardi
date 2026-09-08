# Proposed concepts for the Vardi–Immerman theorem

For every fixed finite relational vocabulary σ, every fixed query arity k,
and every k-ary query Q on finite ordered σ-structures:

**Q is definable in FO(LFP) if and only if Q is decidable in polynomial time.**

The Lean endpoint is:

```lean
axiom capturesPtime {σ : Vocabulary} {k : Nat} (Q : Query σ k) :
    Definable Q ↔ InP Q
```

In Lax, `axiom` declares a statement to be proved separately. These concepts
were approved for proof implementation on 2026-09-08 and are now frozen.
Current proof status is recorded in `CURRENT_STATE.md`.

| Concept | Mathematical content |
|---|---|
| [OrderedStructures](concepts/Lax979537/OrderedStructures.lean) | Finite relational vocabularies, ordered structures, and queries with k distinguished elements. |
| [LeastFixedPoints](concepts/Lax979537/LeastFixedPoints.lean) | Least fixed point of a monotone relation operator; convergence after at most the number of possible tuples. |
| [FixedPointSyntax](concepts/Lax979537/FixedPointSyntax.lean) | FO(LFP) with arbitrary nesting and parameters; every bound relation occurs positively in its defining body. |
| [FixedPointSemantics](concepts/Lax979537/FixedPointSemantics.lean) | Satisfaction and definability; the obligation that syntactic positivity implies monotonicity. |
| [StructureEncoding](concepts/Lax979537/StructureEncoding.lean) | Unary domain size, dense characteristic tables, and distinguished tuple; injectivity and exact length. |
| [PolynomialTime](concepts/Lax979537/PolynomialTime.lean) | A concrete finite Turing machine decides the encoded query language in polynomial time and rejects malformed inputs. |
| [FixedPointEvaluation](concepts/Lax979537/FixedPointEvaluation.lean) | Every fixed FO(LFP) formula has a polynomial-time evaluator. |
| [VardiImmerman](concepts/Lax979537/VardiImmerman.lean) | Every polynomial-time query is FO(LFP)-definable, and the resulting equivalence. |

## Choices affecting the mathematical meaning

- **Order:** represent the universe by `Fin n` with its usual order. Every finite
  ordered structure has a unique such representative up to order-preserving
  isomorphism. Queries may depend on the order.
- **Scope:** relational vocabularies and arbitrary fixed query arities. Boolean
  queries are k = 0. Empty structures and nullary relations are allowed.
  Constant and function symbols are not separate primitives in this version.
- **Logic:** ordinary syntactically positive least fixed points, with nesting,
  negation, and parameters. Positivity is checked through nested binders.
- **Complexity:** data complexity. The formula, vocabulary, arity, machine, and
  polynomial are fixed independently of the input.
- **Encoding:** explicit characteristic tables follow Immerman's encoding
  convention. A unary domain header also handles empty vocabularies without
  compressing an n-element domain into only log n bits. This choice is simpler
  to inspect than introducing a structural arena and conversion theorems.
- **Lax58:** useful infrastructure for a possible RAM implementation in the
  proof package, but not a concept dependency. The main criterion here is
  fidelity to the classical statement and a short, transparent interface.

## Proof scope after concept review

The nine obligations are three fixed-point laws, positivity/monotonicity,
encoding injectivity and length, polynomial evaluation, expressive
completeness, and the final equivalence. All computational implementation
and simulation lemmas belong to the proof package. In particular, neither
polynomial evaluation nor the simulation of Turing computations by formulas
is assumed as a premise of the final theorem.

The main proof work is (1) compiling table evaluation and finite iteration
into actual finite Turing-machine programs and (2) expressing polynomially
bounded Turing computations by a positive fixed point over ordered tuples.
The latter must handle size-zero and size-one structures separately when
using tuples to represent polynomially many positions.

Primary references:
[Immerman, Theorem 2 and its encoding convention](https://people.cs.umass.edu/~immerman/pub/query.pdf),
[Vardi, STOC 1982](https://www.cs.rice.edu/~vardi/papers/stoc82.pdf).
