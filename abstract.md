This submission proves the Immerman–Vardi theorem: on finite
linearly ordered relational structures, a query is definable in first-order
logic with least fixed points if and only if it is decidable in deterministic
polynomial time. The statement covers queries of every fixed arity, including
Boolean queries.

The concepts specify finite ordered structures, syntactically
positive fixed-point formulas and their semantics, an explicit dense binary
encoding, and polynomial time using mathlib's finite Turing machines. Empty
universes and nullary relations are included.

Both computational directions are proved. A concrete Turing-machine decoder
and relation-table evaluator decide each fixed FO(LFP) query in polynomial
time. Conversely, a finite positive rule system represents the initialized,
polynomially bounded computation of an arbitrary finite multi-stack Turing
machine. Its least fixed point is proved equal to the encoded computation;
an accepting-output formula defines the query on sufficiently large domains,
and finite diagrams handle the remaining domains.

The proofs include the fixed-point laws, positivity and monotonicity,
encoding injectivity, and the simulation and runtime arguments. The main
theorems use only Lean's standard background axioms, with no unproved
simulation assumptions.

This is a Lean 4.33 port of [the original Lean 4.30 draft](https://laxarchive.org/lax-979537/).
