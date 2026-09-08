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
evaluator. The next checkpoint below adds its concrete counter and table
primitives; continue with the input decoder and formula evaluator in this language.
Use unary counter stacks and generous table scans to avoid unnecessary
word-size bounds. See the detailed continuation plan in `PROOF_PLAN.md`.

## Counter and table machine checkpoint

Six more proof modules now compile:

- `StackCopy.copy_executes` restores the source, prepends its contents in
  order to the destination, and clears its temporary stack. `copy_store`
  gives a whole-store interface with all unrelated stacks preserved.
- `StackRepeat.repeat_executes` bounds actual executions of a body repeated
  once per counter token. The invariant is stable under counter reads and
  the body; the body may change scratch control. `result_spec` proves the
  counter is empty and scratch is reset on return.
- `StackClear.clear_store` empties a stack with a linear machine bound.
- `StackCompare.less_executes` compares lengths, returns the correct Boolean,
  empties both argument counters, and preserves the rest of the store.
- `StackLookup.lookup_executes` skips a unary index, returns the indexed bit
  or exhaustion, and preserves unrelated stacks. Out-of-range indices are
  included in the specification.
- `StackPower.power_executes` generates n^k unary tokens using one private
  counter per nesting level. It preserves the domain counter and restores
  all private counters; its explicit polynomial depends only on k. This
  includes k=0 and n=0. `cost` is the executable bound; `costPolynomial` is
  its polynomial witness, with `eval_costPolynomial` connecting them.

The two main concept axioms remain open. These primitives are proofs about
actual structured programs compiled to TM2, but they do not yet form the
complete decoder or evaluator.

Next implementation: bounded prefix extraction from the input stack into a
relation-table stack, with a finite-control validity flag for exhaustion.
Use `StackPower` to produce the fixed-arity table-length counters. Parse the
size header once, then each dense relation table and the pointed coordinates;
compare coordinate counters against the domain and reject trailing input.
The existing Lean decoder gives the semantic specification. Follow with
tuple enumeration and the recursive FO(LFP) evaluator.

The expanded `tests/StackMachine.lean` passes. It executes the compiled TM2
machines for source-preserving copy with a nonempty destination, repetition
whose body clears scratch, all counter comparisons for lengths 0–4, indexed
lookup including exhaustion, and powers for n,k in 0–3. The checks include
halting, work-stack cleanup, control reset, and unchanged unrelated stacks.
All newly audited theorem axiom sets contain only the standard propext,
Classical.choice, and Quot.sound (some use fewer). The approved concepts are
unchanged, and no sorry, new axiom, or opaque declaration was introduced.

Full `env LEAN_NUM_THREADS=2 lax build . --replay --no-color` passed in
4m17s (kernel replay 3m55s), covering all six new modules. Lax still reports
eight concepts and seven annotated proofs: six unconditional concept proofs
and the conditional final assembly. No additional main concept obligation
was closed at this checkpoint.

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

## Decoder subroutines checkpoint

Six further modules compile, all for actual structured stack programs:

- `StackTake.takeBits_store` consumes a length counter and extracts a fixed
  prefix in reverse order. Exhaustion pads false bits and sets a sticky
  validity bit to false. `prefix_eq_take` identifies the result with an
  ordinary prefix whenever sufficient input exists.
- `StackReadTable.readTable_executes` composes the power counter, extraction,
  and reversal. It parses one arity-k dense relation table in canonical bit
  order, retains the input suffix, restores work counters, and has a fixed
  polynomial bound. `result_table` and `result_preserves` expose its effects.
- `StackReadRelations.readTables_executes` parses a whole fixed list of
  relation tables, reusing a `Workspace` of private counters. `Fresh` separates
  table stacks, and `Ready` tracks the domain counter and empty work stacks.
  Its runtime is the sum of the individual fixed-arity polynomials.
- `StackCheckedUnary.parse_executes` integrates delimiter checking with the
  same sticky validity convention; its result matches `StackUnary.splitUnary`.
  `checkEnd_executes` rejects trailing input without consuming it.
- `StackCheckBound.checkBound_executes` copies both counters, compares their
  lengths, accumulates validity, and restores all stacks. A spare control bit
  saves prior validity across the comparison and is reset to true.
- `StackCoordinate.parse_executes` parses and validates one pointed
  coordinate. Its bound is linear in the current input and domain lengths;
  `result_valid` is exactly delimiter success and coordinate < domain size,
  conjoined with prior validity.

Store-level interfaces were also added for transfer and comparison. The
expanded compiled-machine tests pass for mixed arities [0,1,2], insufficient
input, nullary relations on empty domains, sticky prior failure, coordinates
inside/outside the domain, and missing delimiters. They check table order,
retained suffixes, control reset, and preservation of unrelated stacks.
All audited results use only standard Lean axioms.

The full decoder is NOT yet assembled or related end-to-end to `Decoding.decode`.
The evaluator and arbitrary TM2-to-formula simulation remain open.

Next: choose a finite stack layout with five reserved ports, a pool of
max-arity counters, relation-table ports, and pointed-coordinate ports. Fold
`StackCoordinate.parse` over the coordinate ports, then sequence checked
header parsing, `readTables`, the coordinate fold, and `checkEnd`. The two
comparison copies can use Workspace.count and Workspace.rev, with Workspace.tmp
as the copying temporary. They are empty between decoder phases.

Use control `BitProgram K ((Unit × Bool) × Bool)`, initially
`((((), true), true), none)`: the inner auxiliary Bool is the comparison spare,
and the final Bool in auxiliary control is sticky validity. Relation parsing
uses `Aux := Unit × Bool`; coordinate parsing uses `Aux := Unit`. Prove input
suffix lengths never grow, bound parsed n by original input length, and lift
the fixed-polynomial costs accordingly. The remaining semantic bridge must
prove exact acceptance of canonical encodings, including malformed input.
The existing `Decoding.decode`/`DecisionProcedure.checkedDecode` specifications
are available; do not assume that bridge or treat these subroutine tests as
the complete machine proof.

Checkpoint validation: the expanded `tests/StackMachine.lean` passes,
including the final trailing-input tests. `checkEnd_executes` uses only
Quot.sound; the other new audited results use at most the standard three
Lean axioms. Full `env LEAN_NUM_THREADS=2 lax build . --replay --no-color`
passed in 5m13s (kernel replay 4m45s), with eight concepts and seven annotated
proofs. The concepts are unchanged from cf16245. The two main directions
remain open, and nothing has been submitted or published.

## Assembled finite decoder checkpoint

The finite decoder is now assembled, with four new checked modules:

- `StackReadCoordinates`: iteration over all pointed coordinates, preservation
  of previous data, and a linear bound for fixed query arity. Together with
  new `StackReadRelations` lemmas, this proves input suffixes never grow and
  the private workspace is reusable between phases.
- `StackDecoder`: a `Layout` contains the workspace, tables, coordinates,
  distinctness, freshness, and fixed arity bounds. `decode` sequences checked
  unary header parsing, all relation tables, all pointed coordinates, and
  trailing-input rejection. `decode_executes` proves termination on every
  input within one polynomial in the ORIGINAL input length, reaching its
  explicit pure store result. No correctness of that store result relative
  to semantic structures is assumed in this theorem.
- `FiniteDecoder`: an explicit finite port type for every vocabulary σ and
  query arity k: Fin 5 plus a counter pool of size σ.sum, relation ports, and
  coordinate ports. Every arity is at most σ.sum. `layout`, `program`, and
  `decoderMachine` instantiate all abstract layout obligations.
  `program_executes` gives the polynomial structured execution, and
  `decoder_runs` transfers it to actual TM2 steps from `Turing.initList` to the
  halted result configuration. `cost` is an executable polynomial bound,
  related to the polynomial witness by `eval_costPolynomial`.
- `DecoderSoundness`: reverse parsing laws for unary fields, dense relation
  tables, and pointed tuples. Tuple enumeration has no duplicates, and
  `readTable_map` reconstructs each dense table exactly. `decode_sound` proves
  `Decoding.decode σ k w = some A → encode A = w` for every input, and
  `checkedDecode_eq_decode` removes the extra serialization check semantically.
  No approved concept was changed, nor was the existing decision function
  weakened or redefined.

`tests/DecoderMachine.lean` runs the assembled finite TM2, comparing its result
with `Decoding.decode`, including every stored table and coordinate on valid
inputs and workspace cleanup on all inputs. Mixed/nullary relations, empty
domains, out-of-range or missing coordinates, trailing data, and insufficient
table input are covered. It also checks every bit string of length 0–5 for
signatures [0,1] with query arity 1 and [2] with query arity 0. These tests
pass. Audited theorems use only the standard Lean axioms.

The GENERAL machine/semantic-decoder correspondence remains to be proved:
the tests provide examples, not that theorem. The concrete decoder's explicit
result still needs to be shown to have validity true exactly when
`Decoding.decode` succeeds, with matching domain size, relation bit tables,
and unary pointed coordinates. `DecoderSoundness.decode_sound` handles the
canonical-encoding half AFTER this correspondence; it does not establish
that correspondence by itself. Then implement the formula evaluator over
the retained tables/counters. Both main concept obligations remain open.

Next proof target: observe the final `StackDecoder.result (FiniteDecoder.layout σ k)`
as an optional decoded structure. Relate the sticky validity convention and
stored payloads to the semantic parser phase by phase. The existing
`StackReadRelations.result_preserves`, `StackReadCoordinates.result_preserves`,
`StackReadTable.result_table`, `StackCoordinate.result_valid`, and unary
reverse parsing laws provide the local ingredients. Distinct finite port
constructors eliminate all cross-phase aliasing cases. The counter pool uses
σ.sum solely for convenient fixed layout bounds; runtime needs only polytime.

Checkpoint validation: `tests/DecoderMachine.lean` passes, including the
concrete `decoder_runs` axiom audit. Full
`env LEAN_NUM_THREADS=2 lax build . --replay --no-color` passed in 5m46s
(kernel replay 5m25s): eight concepts and seven annotated proofs. All four
new modules were included. The approved concepts remain unchanged, both
main concept obligations remain open, and no submission was made.
