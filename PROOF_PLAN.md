# Proof implementation plan

The user authorized proof implementation and completion on 2026-09-08.
The approved concept files must remain unchanged.

1. Prove leastness, the fixed-point equation, and finite convergence.
2. Prove positivity implies monotonicity through arbitrary nested binders.
3. Prove the explicit encoding's length and injectivity; construct a decoder.
4. Define and verify finite relation-table evaluation, including nested LFP.
5. Implement polynomial evaluation on the concrete finite Turing model.
6. Express polynomial Turing computations by positive fixed-point formulas,
   including arbitrary fixed query arity and the small-domain cases.
7. Derive the final equivalence, audit all assumptions, replay with Lax, and
   finish submission metadata and source publication as authorized.

A theorem with unresolved Lax assumptions is not a completed proof of the
full result. No self-assumption, circular assumption, sorry, or weakened
concept may be used to report completion.


## Checked checkpoint

Steps 1–4 are complete at the level of semantic correctness, including a
verified total decision function on encoded inputs. Input-size bounds,
variable renaming, and tuple-order formulas are also proved. Step 7 has a
conditional final assembly with exactly the two main directions as open
assumptions. Steps 5 and 6 are the remaining substantial constructions;
see `CURRENT_STATE.md` for exact targets and validation evidence.
