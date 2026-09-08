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

## Runtime and literature decisions

The user explicitly requested coarse polynomial bounds, not sharp runtime
bounds. Use generous polynomial overhead for scans, copies, tuple arithmetic,
and compilation. `PolynomialBounds.exists_power` absorbs every fixed
polynomial into a power of the domain size for sizes at least two.

Use Immerman (1986), section 3, Theorem 2 and Lemma 3.1 as the main guide:
encode time/positions by tuples, define the initial row in FO, use a positive
local transition rule, prove the stage invariant, and read acceptance. This
direct positive-LFP route avoids unnecessary IFP/LFP collapse machinery.
Libkin, sections 9.1–9.2 and 10.4 (Theorem 10.14, pages 192–194), supplies
complementary input-encoding and machine-transition details. Neither source
supplies our concrete mathlib TM2 compiler; that bridge must be proved.

## New constructions

- `EvaluationWork.work_le_input_length`: materialized-table operation charges
  are bounded by a fixed polynomial in input length, including nested LFP.
  This is explicitly NOT yet a concrete TM2 step bound.
- `ComputationTableau.leastFixedPoint_iff`: the positive local operator gives
  exactly the bounded computation. The stronger `stage_iff` characterizes
  every stage; a nonempty dependency neighborhood is required.
- `PositiveRules.eval_closure`: a finite set of FO-guarded positive rules
  compiles into the approved syntax and defines its least closed relation.
- `TupleAddresses` and `AddressFormulas`: big-endian tuple addresses, FO
  numerical order/successor/zero, fixed numerals, and exact domain size.
- `FiniteExceptions.bounded_definable`: every query on structures of size at
  most a fixed N has an explicit finite FO definition, including pointed
  queries, nullary relations, and the empty domain.

Connect these constructions to concrete machines. The rule compiler currently
has no additional free parameters inside its rules; pointed input parameters
must be handled when instantiating it, or the proof-only compiler generalized.
No change to the approved concept syntax is needed for that generalization.
