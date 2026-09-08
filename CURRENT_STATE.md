# Vardi–Immerman proof implementation

Updated: 2026-09-08.

The user approved the eight concept files and authorized proof implementation
and completion of the submission. The concepts are frozen and unchanged from
commit cf16245. No further permission is needed for proof work. The task is
not complete: both main computational directions remain open.

The user has now explicitly made completion and submission our active goal.
They also emphasized that any polynomial runtime bound is sufficient; do not
spend effort optimizing constants or exponents. No token budget was requested.

## Mathematical interface

Read `PROPOSED_CONCEPTS.md`. The theorem is `Definable Q ↔ InP Q` for every
fixed finite relational vocabulary and query arity on finite ordered
structures. Inputs use a unary domain-size header and dense relation tables.
Lax58 was considered but is not a concept or proof dependency. The user's
criteria are fidelity to the original formulation and clarity of concepts.

## Proved

Six concept statements have proofs with no outstanding Lax assumptions:

- LeastFixedPoints.fixedPoint
- LeastFixedPoints.least
- LeastFixedPoints.finiteConvergence
- FixedPointSemantics.positiveBodyMonotone
- StructureEncoding.encodeInjective
- StructureEncoding.encodeLength

`VardiImmerman.capturesPtime` has an annotated proof relative to precisely
`FixedPointEvaluation.evaluationInP` and `VardiImmerman.ptimeDefinable`.
This conditional assembly must not be described as a complete proof.

Further proved implementation results, all in the proof package:

- `Decoding.decode_encode`: executable parsing round-trips every valid input.
- `TableEvaluation.evaluate_correct`: executable relation-table evaluation
  agrees with the approved FO(LFP) semantics. Each LFP round materializes a
  list of satisfying tuples; lookups do not re-evaluate previous rounds.
- `DecisionProcedure.checkedDecode_sound`: accepted representations are exact
  canonical encodings. `decideFormula_correct` verifies the resulting total
  bit-string decision procedure, including malformed-input rejection.
- `InputSize`: the encoded size is at least the domain size, and at most an
  explicit polynomial in it for fixed vocabulary and query arity.
- `SyntaxOperations`: capture-avoiding renaming through element quantifiers
  and LFP binders preserves semantics, admissibility, and positivity.
- `TupleOrder`: finite conjunction/disjunction and a verified admissible FO
  definition of lexicographic tuple order, independent of domain size.
- `PolynomialBounds.exists_power`: a fixed polynomial is strictly dominated
  by one power of n for all n ≥ 2; includes polynomial evaluation monotonicity.
- `EvaluationWork.work_le_input_length`: an explicit conservative charge for
  the existing materialized-table algorithm is polynomial in encoded input
  length. It covers nested LFP, tuple/table scans, and bounded environments.
  This charge is NOT a TM2 machine step bound and is not advertised as one.
- `ComputationTableau.stage_iff` and `leastFixedPoint_iff`: every stage of a
  positive local transition operator contains exactly the intended prefix of
  the computation, with no spurious cell symbols. This is a generic local
  system, not yet an instantiation for arbitrary finite TM2 machines. The
  number of dependencies d is required positive for the exact stage invariant.
- `FormulaMacros`: first-order context copying, block existential binding,
  and preservation of semantics, admissibility, positivity, and FO syntax.
- `PositiveRules.eval_closure`: a finite list of FO-guarded positive Horn
  rules compiles to a real admissible formula in the approved concept syntax,
  with a proof that it defines the least closed relation. No Lax assumptions.
- `TupleAddresses.address_lt_iff`: an explicit big-endian equivalence between
  k-tuples over Fin n and Fin (n^k), respecting the existing FO lex order.
- `AddressFormulas`: FO definitions and semantic proofs for address zero,
  successor, fixed numerals, size bounds, and exact domain sizes.
- `FiniteExceptions`: finite FO diagrams characterize each canonical pointed
  structure; `bounded_definable` covers any query on sizes ≤ N, and
  `definable_of_above` patches a definition valid for sizes > N. This includes
  nullary relation bits on the empty universe.

## Remaining main proof obligations

1. `FixedPointEvaluation.evaluationInP`: supply an actual bundled finite TM2
   machine and polynomial step bound for the verified decision procedure.
   Correct executable Lean code is not itself a proof of this machine claim.
   A sufficient target is
   `Nonempty (Turing.TM2ComputableInPolyTime id (fun b => [b])
     (DecisionProcedure.decideFormula φ))` for every fixed formula φ.
   The correctness half is already `decideFormula_correct`.
2. `VardiImmerman.ptimeDefinable`: construct a positive fixed-point formula
   for an arbitrary polynomial-time finite TM2 computation. Renaming and
   tuple ordering, numerical address formulas, a generic positive tableau
   invariant, and a positive-rule syntax compiler are available. The remaining
   work is the actual TM2 instantiation: input-bit interpretation for the
   chosen encoding, finite-control/symbol encoding, and machine simulation.
   Small-domain exceptions now have a proved general solution in
   `FiniteExceptions.definable_of_above`.

Do not mistake a rule/operator correspondence assumption for the machine
simulation proof. The current positive-rule compiler has no extra parameters
inside rules; pointed input parameters must be handled during instantiation
or by generalizing this proof-only compiler. Approved syntax already supports
them. The finite-exception construction does support arbitrary query arity.

The inspected mathlib `TM2ComputableInPolyTime` module does not provide a
ready-made compiler for the relation-table evaluator. Lax51 has substantial
RAM/TM simulation proofs, and Lax13Proofs has an IMP compiler, which may help
as explicitly pinned proof dependencies; neither currently supplies this
formula evaluator or the descriptive-complexity direction. No dependency
was added speculatively, and no imported `proof_wanted` assertion was used.

## Validation

- First full `env LEAN_NUM_THREADS=2 lax build . --replay --no-color` passed
  in 4m02s: eight concepts and seven annotated proofs. This covered all six
  unconditional concept proofs, the conditional final assembly, and the
  verified bit-string decision procedure.
- `lake env lean ../tests/Evaluator.lean` passed from `proofs/`: forward,
  backward, and reflexive directed reachability; empty and trailing-data
  rejection; empty universes; and both truth values of nullary relations.
- The same check prints the axiom sets of all six unconditional statement
  proofs and `decideFormula_correct`: only propext, Classical.choice, and
  Quot.sound occur (some proofs use a smaller subset).
- Input-size, renaming, and tuple-order helpers subsequently compiled.
- Final replay covering the complete checkpoint also passed: full
  `env LEAN_NUM_THREADS=2 lax build . --replay --no-color`, 2m48s, eight
  concepts and seven annotated proofs. This includes the input-size,
  renaming, and tuple-order helper modules. `lake build` completed 1,226 jobs.

## Local submission state

Provisional id: lax-979537. No remote is configured, authors remain unfilled,
and nothing has been submitted or published. Do not publish this as a completed
Vardi–Immerman formalization while the two computational directions are open.
The preview uses http://localhost:8125/lax-979537/index.html when running.

Continue with the two main obligations above. Do not change the approved
concepts, introduce sorry or new proof axioms, or use circular assumptions.

## Current iteration checks

The eight new helper modules listed above compile. A complete `lake build`
passed with 1,236 jobs before the final small-exception patching lemma; that
lemma also compiled subsequently. `tests/Constructions.lean` checks generated
reachability rules, tuple successor carries and boundaries, exact domain
sizes, pointed diagrams, and nullary predicates on an empty universe, and
prints the axiom sets of the main new results. The construction tests passed;
all eight audited theorem axiom sets contain only propext, Classical.choice,
and Quot.sound. The test inputs needed explicit Fin 3 annotations; this was
a test elaboration fix, not a proof or concept change.

Full `env LEAN_NUM_THREADS=2 lax build . --replay --no-color` passed in 3m12s
(kernel replay 2m35s): eight concepts and seven annotated proofs. All new
helper modules were included. The number of main annotated proofs is
unchanged: the two computational directions are still open, and the final
equivalence remains conditional on them.
The original `tests/Evaluator.lean` also passed again after this checkpoint.

## Concrete next implementation step

The direct structured stack-program compiler is now implemented and checked:

- `StackProgram`: explicit structured syntax over the TM2 operations, finite
  syntax-tree label types, continuation compilation, counted terminating
  executions, and `compile_correct` for arbitrary label embeddings.
- `StackProgram.machine` is an actual `Turing.FinTM2`, and
  `program_polytime` produces exactly `TM2ComputableInPolyTime` from a
  polynomial bound on these program executions. It also requires the correct
  input/output stack convention, work-stack cleanup, and finite-control reset.
- `StackTransfer`: a compiled linear bit-transfer routine with arbitrary
  auxiliary finite state and framed unrelated stacks; `reverse_polytime`
  proves an end-to-end instance of the exact complexity interface.
- `StackUnary`: a compiled linear unary-header parser. It consumes the
  delimiter, preserves the remaining input, stores the count on a separate
  stack, and signals a missing delimiter. `splitUnary_correct` connects it
  to the existing executable `Decoding.readUnary`; `parse_executes` is proved
  for arbitrary inputs, not only well-formed ones.

No imported `proof_wanted` assertion or Lax assumptions are used in this
compiler. The compiler is general, but it does NOT yet contain the formula
evaluator. Continue with preserving copy, unary comparisons, bounded loops,
dense-table lookup, and the formula evaluator in this structured language.
Use unary counter stacks and generous table scans to avoid unnecessary
word-size bounds. See the detailed continuation plan in `PROOF_PLAN.md`.

The reverse expressive direction also remains open; the concrete TM2-to-
tableau instantiation has not advanced in this compiler iteration.

Validation for this iteration: `StackProgram`, `StackTransfer`, and
`StackUnary` compile. `tests/StackMachine.lean` passed: it directly runs
compiled machines on reversal, branching, nested loops, and valid/malformed
unary headers. The six audited results use at most propext, Classical.choice,
and Quot.sound; `splitUnary_correct` uses no axioms. Full Lax replay passed in
3m46s (kernel replay 3m26s), with eight concepts and seven annotated proofs.
All three new machine modules were included. The two main computational
directions remain open; this successful replay does not close them.

Implementation detail for the next copy routine: move `src` into an empty
temporary stack using `transfer`; then pop that temporary stack while pushing
each saved bit onto both `src` and `dst`. This restores `src`, prepends the
same bit string to `dst`, and clears the temporary stack. A three-stack store
invariant and pairwise-distinct indices suffice; all other stacks and the
Aux part of finite control remain framed. Such a linear preserving copy then
supports unary-bound loops and non-destructive table scans.
