This submission formalizes the Vardi–Immerman theorem's interface: on finite
linearly ordered relational structures, a query is definable in first-order
logic with least fixed points if and only if it is decidable in deterministic
polynomial time. The statement covers queries of every fixed arity, including
Boolean queries.

The approved concepts specify finite ordered structures, syntactically
positive fixed-point formulas and their semantics, an explicit dense binary
encoding, and polynomial time using mathlib's finite Turing machines. Empty
universes and nullary relations are included.

Proof development is in progress. The fixed-point laws, finite convergence,
positivity/monotonicity, and encoding injectivity and length are proved.
An executable decoder and a materialized relation-table evaluator are
verified, yielding a correct total decision function on bit strings.
The two main computational directions remain open: polynomial-time Turing
machine evaluation and definability of arbitrary polynomial-time computations.
The final equivalence is currently proved relative to these two obligations.
This is not yet a complete proof of the Vardi–Immerman theorem.
