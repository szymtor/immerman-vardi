# Vardi–Immerman proof implementation

Updated: 2026-09-08.

The user approved the eight concept files and authorized proof implementation
and completion of the submission. The concepts are frozen and unchanged from
commit cf16245. No further permission is needed for proof work. The task is
not complete: the reverse machine-to-formula direction remains open.

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

Seven concept statements have proofs with no outstanding Lax assumptions:

- LeastFixedPoints.fixedPoint
- LeastFixedPoints.least
- LeastFixedPoints.finiteConvergence
- FixedPointSemantics.positiveBodyMonotone
- StructureEncoding.encodeInjective
- StructureEncoding.encodeLength
- FixedPointEvaluation.evaluationInP

`VardiImmerman.capturesPtime` has an annotated proof relative to precisely
`VardiImmerman.ptimeDefinable`; its forward direction uses the proved evaluator.
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

`FixedPointEvaluation.evaluationInP` is now proved by the actual bundled
finite TM2 and polynomial execution bound in `FormulaDecision`. Its complete
input/output convention and malformed-input rejection are proved for every
bit string. The remaining main obligation is:

1. `VardiImmerman.ptimeDefinable`: construct a positive fixed-point formula
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
Vardi–Immerman formalization while the reverse computational direction is open.
The preview uses http://localhost:8125/lax-979537/index.html when running.

Continue with the reverse simulation above. Do not change the approved
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

## Decoder correctness completed

The general decoder correspondence is now proved, not merely tested:

- `RawDecoding.Data` is a proof-side observation of size, dense bit tables,
  and coordinate values. `decode_eq` identifies its parser exactly with
  `Decoding.decode.map RawDecoding.view`. It does not change acceptance.
- `DecoderAgreement.tables_agree` and `coords_agree` prove agreement of the
  machine's sticky validity bit and all retained payloads with those parser
  phases. `decode_agree` composes them for any well-formed fixed layout.
- `finite_agree` specializes to the actual finite decoder for arbitrary σ,k.
  `accepts_iff_encoding` proves exact recognition of canonical pointed
  structure encodings. `finite_data` proves correct domain, tables, and
  coordinate values on every successful semantic decode.
- `DecoderCorrectness.Represents A s` is the evaluator's input contract:
  a unary domain counter, empty reusable work stacks, empty input stack,
  exact canonical relation-bit tables, and coordinate-counter lengths equal
  to the pointed coordinates. `result_represents` proves this contract.
- `decoder_correct` combines bounded actual TM2 execution from `initList`,
  exact acceptance, and `Represents` for every encoded input. This closes
  the complete decoder bridge. The machine also terminates and rejects
  every malformed input within its fixed polynomial bound.

`tests/DecoderMachine.lean` passes with the new proofs imported. All audited
new results use only propext, Classical.choice, and Quot.sound. The three new
modules are imported by the proof root. No concept was changed.

Next major forward-direction step: the formula evaluator over this retained
representation. Compile a generalized admissible `RawFormula σ m ρ` with
element-counter ports and bound-relation-table ports. The program must be
fixed by the syntax/layout, independently of the input size and structure.
Preserve input tables and environment counters, use fresh local slots for
bound variables/LFP tables, and return the Boolean result with local workspace
cleaned. `TableEvaluation.evaluate_correct` is the semantic specification;
the old `EvaluationWork` charge remains only an algorithmic bound until
connected to actual compiled executions.

A practical next primitive is tuple iteration with one copied domain counter
and a fresh increasing unary coordinate at each fixed nesting level. It
should execute a callback for tuples in `StructureEncoding.tuples` order,
preserve domain/environment stacks, and clean all private counters afterward.
Full scans suffice for atomic table lookup; no rank arithmetic or sharp
runtime exponent is required. The same iterator serves quantifiers and
materialized LFP stages. A fixed formula determines a finite collection of
private slots. Keep the complete evaluator and reverse simulation as the
remaining main obligations; decoder completion is not theorem completion.

The standalone `FiniteDecoder.Port σ k` has no evaluator-specific private
ports. Extend it by a finite sum when assembling the evaluator. A stack-port
renaming theorem for `StackProgram.Program` along an injection can reuse the
decoder execution and representation proof while framing the extra ports;
alternatively instantiate the already-generic `StackDecoder.Layout` over the
extended type. The control state can remain the existing finite Boolean
registers, with saved intermediate values on private bit stacks. Do not make
the compiled program depend on n, the structure, or its runtime contents.

Checkpoint validation: `tests/DecoderMachine.lean` passes with all general
agreement/correctness axioms audited. Full
`env LEAN_NUM_THREADS=2 lax build . --replay --no-color` passed in 6m16s
(kernel replay 5m48s), including all three new modules. Lax reports eight
concepts and seven annotated proofs. The decoder obligation is complete,
but the two main computational directions remain open and the final theorem
is still conditional on them. No concepts changed and nothing was submitted.

## Evaluator machine combinators

The forward direction now has these additional verified stack programs:

- `StackFor.forValues_executes`: copy a domain counter, visit unary
  coordinates 0 through n-1 in order, execute a bounded callback at each
  valid coordinate, and clean the private counter/coordinate/temporary slots.
  The result is specified by `foldRange`, identified with the ordinary list
  fold by `foldRange_zero_eq`. The callback may change a semantic payload,
  represented by an arbitrary family of stores; it preserves loop counters.
  This proves one-coordinate iteration, not yet arbitrary tuple iteration.
- `StackRename.rename_executes` and `executes_in_sum`: inject a program into
  a larger stack layout at unchanged execution cost, preserving every extra
  stack. This allows the complete decoder to run alongside evaluator ports.
- `StackBoolean.Returns`: the evaluator contract returns a Boolean in the
  existing control register, resets spare/scratch registers, preserves outer
  auxiliary state, and restores every stack. `binary_returns` and
  `negate_returns` implement Boolean composition with saved answers on a
  stack, whose previous contents are restored as well.
- `StackAtomic.lessValue_returns` and `equalValue_returns`: evaluate order
  and equality of unary coordinate counters with polynomial execution bounds
  and full stack restoration. Repeated-variable cases are handled by a
  static port-equality branch, so x = x and x < x are covered.
- `StackExists.existsValues_returns`: run a bounded Boolean evaluator once
  for each domain element, accumulate disjunction, and restore all stacks,
  including prior accumulator contents. It returns `(List.range n).any b`,
  with `any_range_iff` connecting this to existential truth. The body proof
  is required only for i < n; n = 0 returns false without running the body.

All these are actual `StackProgram` executions and hence transfer through
the existing verified TM2 compiler. They are not yet the recursive compiler
for every admissible FO(LFP) formula. Program syntax depends only on fixed
ports and subprograms; n and the semantic predicate occur only in proofs.

Next: develop tuple enumeration/table access and materialization, then
compile formula syntax with a finite private workspace and a representation
invariant for free elements and bound relations. The quantifier combinator
already provides the machine construction for `exists'`, conditional on the
recursive body evaluator contract. A useful layout has fresh coordinates,
saved Boolean slots, and LFP table buffers allocated by syntax; `StackRename`
handles enlarged layouts without duplicating decoder proofs. Dense relation
access may use full scans; coarse polynomial overhead remains sufficient.
Both main concept obligations are still open, and submission is pending.

`tests/EvaluatorMachine.lean` passes. It runs actual compiled machines for
ordered domain traversal (n = 0–5), equality/order for all pairs of lengths
0–4, and existential equality for domain sizes 0–4 and parameter values 0–5.
It checks complete stack restoration, including populated saved-answer
stacks. Four valid/malformed inputs exercise the full decoder after port
renaming into a larger layout with populated extra stacks. A symbolic proof
also composes `equal_returns` with `existsValues_returns` for arbitrary n,m:
the resulting program returns `decide (m < n)` with its derived execution
bound. Audited new theorems use only standard Lean axioms. Full
`env LEAN_NUM_THREADS=2 lax build . --replay --no-color` passed in 7m07s
(kernel replay 6m55s), including all five new proof modules. Lax reports
eight concepts and seven annotated proofs, still six unconditional concept
proofs and the conditional final assembly. Concepts remain identical to
cf16245, both main directions remain open, and nothing was submitted.

## Tuple traversal and materialized table rounds

The machine now has the following further proved constructions:

- `StackTuples.forTuples_executes` nests the domain loop at a fixed list of
  counter/coordinate pairs. Its callback executes once per tuple, in order,
  with a uniform bound B. It restores every loop stack and clears scratch.
  Semantic payload changes are specified by `foldTuples`; the callback
  preserves the active tuple and remaining loop counters. It is required
  only for tuples whose coordinates are below n.
- `tuples_eq_canonical` proves that this order is precisely the list in the
  approved `StructureEncoding.tuples`, observed as lists of natural-number
  coordinate values. `foldTuples_eq_foldl` identifies callback accumulation
  with its ordinary list fold. Nullary traversal executes once, even over
  n = 0; positive arity over n = 0 executes no callbacks.
- `StackTuples.costPolynomial` proves polynomial bounds for actual compiled
  executions, given a polynomial bound on the callback. The polynomial is
  fixed by the arity and callback bound. `packTuple_state`, `packTuple_fresh`,
  `packTuple_setStack`, and scratch-normalization lemmas support composing
  callbacks with independent input and output stacks.
- `StackMaterialize.materialize_executes` runs a Boolean evaluator for
  each tuple, stores each answer once in a reverse buffer, then transfers
  the completed dense table into canonical order. The theorem restores all
  stacks except the output, where it prepends the table to prior contents.
  The reverse buffer is required initially empty and is returned empty.
  Its body premise is a concrete bounded `StackBoolean.Returns` execution
  for each valid tuple and arbitrary already-emitted rows. `table_length`
  and `eval_costPolynomial` connect the result and cost to n^k.
- `StackTableRound.round_executes` constructs a complete next table while
  retaining the old current table for body evaluation. It then clears the
  old table and installs the new table, using two transfers to preserve
  canonical order. All buffers and loops are restored. The bound depends
  polynomially on the callback cost, n^k, and old-table length; no bound is
  assumed on how many rows of the new table differ from the old one.

These are actual machine primitives for materialized LFP evaluation, not
the full LFP compiler or either main concept theorem. The next substantial
forward steps are table access, bounded iteration of the table-round program
for n^k stages starting from the all-false table, and formula induction with
a finite workspace. The previous claim that tuple traversal and individual
table rounds were still unimplemented is superseded by this checkpoint.

A direct stage-loop construction can reuse `StackPower` to prepare a unary
n^k bound, `StackFor.forValues` to run a fixed table-round body under that
bound, and `StackClear` for cleanup. Its semantic fold is ordinary iteration
of the table transformer. The loop's extra unary round coordinate is harmless
polynomial overhead; no precise bound or optimized counter representation is
needed. The initial all-false table can be materialized with `answer false`.
For table access, either full scans with tuple matching or unary tuple rank
followed by the existing indexed lookup suffice. The latter can use Horner
updates `index := n * index + coordinate` implemented by bounded copies.
These are next implementation options, not proved constructions yet.

`tests/TupleMachine.lean` checks actual compiled tuple enumeration for
arities/domain sizes 0–3, and table construction for arities 0–2/domain sizes
0–3. It verifies order, emitted values, all private-stack cleanup, retained
domain data, and populated unrelated stacks. A symbolic proof instantiates
the materializer with the existing atomic comparison evaluator for every n,
producing the full table of x < y with the derived bound. Round tests check
that the old table remains available throughout construction and that a
nonconstant new table is installed without reversal. All tests pass, and
axiom audits use only standard Lean axioms. Full
`env LEAN_NUM_THREADS=2 lax build . --replay --no-color` passed in 7m14s
(kernel replay 6m56s), including all three new modules. Concepts remain
identical to cf16245. Lax still reports eight concepts and seven annotated
proofs: the final assembly depends on the two open computational directions.
No submission was made; the full goal remains active.

## Bounded materialized LFP iteration

The complete iterative part of the LFP machine is now implemented and proved:

- `StackStages.stages_executes` prepares n^k with the verified power routine,
  uses a fixed bounded loop to execute a supplied stage body exactly n^k
  times, and clears all stage counters. Its result is the mathematical
  function iterate of the semantic payload transformer. The program contains
  neither n nor an input-dependent stage count as a control constant.
- `StackInitialTable.initialize_executes` constructs n^k false bits using
  the materializer with the constant-false evaluator. The empty relation has
  one false bit at arity zero, including over the empty domain.
- `StackTableStages.tableStages_executes` specializes the stage loop to
  actual `StackTableRound` executions. A family of semantic payloads has
  dense tables of length n^k; each body callback supplies a bounded Boolean
  answer for one valid tuple in the current payload. The theorem derives
  complete repeated table updates from these callback executions; it does
  not assume correctness or executions of the stage loop.
- `StackLfpTables.run_executes` composes false-table initialization and the
  n^k rounds. It retains the final table and restores every other stack.
  Fixed polynomials bound actual executions, given a polynomial callback
  bound. Final lookup and deletion of the retained private table remain the
  responsibility of the full LFP constructor.
- `DenseTables` connects list-of-tuples semantic relations to their dense
  bit tables. Natural-list tuple observations are injective; every valid
  natural tuple represents a Fin-valued tuple, including empty cases.
  `predicate_values` transfers callback semantics to that representation,
  and `dense_next` relates materialized bits to filtering canonical tuples.
- `StackSemanticRounds.semantic_rounds_executes` now proves that the retained
  machine table is exactly `dense (TableEvaluation.rounds (next p) (n^k))`.
  The recursive body premise uses ordinary Fin-valued tuples and the current
  semantic relation. This is the same rounds operation used by the existing
  verified FO(LFP) semantic evaluator.

The remaining forward-direction work is table lookup, the general formula
compiler with finite private-port allocation and input invariants, and final
machine cleanup/output assembly. The iterative LFP subroutine above does not
by itself prove `evaluationInP`. The reverse machine-to-formula simulation
also remains open, and the final concept theorem remains conditional.

`tests/StageMachine.lean` checks actual machines for domain sizes 0–3 and
arities 0–2. The generic stage loop emits successive stage coordinates, so
the tests check both its n^k count and traversal order. Table iteration is
tested with a toggling transformer to detect the exact number of rounds;
that deliberately nonmonotone transformer is a test of the general bounded
iteration program, not a claimed positive LFP formula. A symbolic proof
instantiates false-table initialization and all n^2 table stages for every n,
using a real peek operation on the retained current table as its callback.
The tests check all temporary-stack cleanup and populated unrelated stacks.
Dense-table examples include nullary and empty-domain cases and a nonconstant
order table. All tests pass, and the axiom audit reports only standard Lean
axioms. Full `env LEAN_NUM_THREADS=2 lax build . --replay --no-color` passed
in 7m31s (kernel replay 7m20s), including all six new proof modules. Concepts
remain identical to cf16245. Lax still reports eight concepts and seven
annotated proofs; both main computational directions remain open and the
final assembly remains conditional. Nothing was submitted.

Next table-access option: accumulate a unary tuple rank with fixed Horner
steps `index := n * index + coordinate`, then copy the source table and use
the existing linear skip/lookup routine. One Horner step can transfer the
old index into a private counter, repeat domain-copy once per old-index
token, and append a copy of the coordinate counter. Input coordinate ports
may repeat; only their separation from the workspace is needed. At arity
zero the index is zero. `StackLookup.skip_executes` already supports the
evaluation control type, so a Boolean-returning final pop and cleanup can
reuse it without a general change-of-control compiler. This is the next
implementation plan, not a proved lookup constructor yet.

## Tuple lookup and complete LFP value constructor

The planned table-access constructor is now implemented:

- `StackHorner.step_executes` performs one unary update n*a+v by moving
  the old index into a counter, copying the domain once per token, and
  copying the coordinate. Source counters and all temporary stacks are
  restored. No input-dependent value is captured in a control function.
- `StackIndex.build_executes` folds these updates over a fixed coordinate
  port list. Ports may repeat. Starting from zero, its execution cost is
  bounded by a polynomial depending only on tuple arity.
- `TupleRank.rank_address` identifies the Horner result with the existing
  big-endian tuple address. `canonical_at_address` proves that this index
  selects the exact tuple from the approved canonical enumeration; it is
  proved by constant-length block lookup, not assumed from lexicographic
  order. `table_at_rank` gives the selected dense relation bit.
- `StackReadBit.readBit_executes` copies a table, skips a unary index,
  returns the bit (false on exhaustion), and clears the copied suffix and
  index. The original source table and unrelated stacks are preserved.
- `StackTableLookup.lookup_returns` combines rank construction with this
  read into an actual bounded Boolean evaluator for arbitrary dense
  relations. It handles repeated arguments and nullary relations and
  restores every stack, including all private lookup workspace.
- `StackLfpValue.evaluate_returns` completes the LFP machine constructor:
  initialize the false table, perform n^k materialized rounds, read the
  queried tuple, and delete the final private table. The result is membership
  in `TableEvaluation.rounds`, and every original stack is restored. The
  recursive body contract is a bounded actual Boolean execution for each
  Fin-valued tuple in the represented current relation. No simulation or
  stage-loop correctness assumption replaces that recursive body contract.

The forward compiler now has machine constructors for every raw formula
case: constants, equality/order, input and bound relation lookup, negation,
conjunction, existential quantification, and materialized LFP evaluation.
The general formula compilation/representation induction and final decoder,
cleanup, and output composition still need to be implemented. This does not
yet prove `evaluationInP`. The reverse simulation and submission are open.

`tests/LookupMachine.lean` runs compiled machines for unary Horner steps,
three-coordinate index construction with repeated ports, copied table reads
including empty/exhausted tables, and complete tuple lookups at arities 0–3.
It checks the complete LFP value constructor on the constant monotone
transformer x < y, including repeated query arguments and final table cleanup.
The tests cover small and empty domains where the corresponding tuple exists,
and verify populated unrelated stacks. All tests pass. The new theorem axiom
audits report only standard Lean axioms. Full
`env LEAN_NUM_THREADS=2 lax build . --replay --no-color` passed in 9m24s
(kernel replay 8m54s), including all six new modules. Concepts remain identical
to cf16245. Lax still reports eight concepts and seven annotated proofs;
both main computational directions remain open and the final assembly is
conditional on them. Nothing was submitted.

## Next: general formula compiler

Compile `RawFormula σ m ρ` with the existing evaluation control type and a
workspace fixed solely by syntax. A useful implementation avoids natural
offset arithmetic: define a finite `Work φ` type recursively. Use separate
constructors for a conjunction's saved bit/left/right work, an existential's
counter/coordinate/tmp/accumulator/child work, and an LFP's seven core ports,
power counters indexed by Fin k, tuple counters/coordinates indexed by Fin k,
and child work. Leaf equality/order and table lookup use fixed finite work
types. Derive Fintype/DecidableEq recursively. The compiler can then accept
an injective port map `Work φ → K` into any ambient layout. Constructor
disjointness supplies private-port freshness without proving arithmetic
facts about cumulative workspace offsets. This compiler is not written yet.

The general invariant should represent a structure A, an element environment
v, and a `TableEvaluation.TableEnv` η by a unary domain stack, unary element
stacks, canonical input relation tables, and dense tables for bound relations.
Require private workspace ports to be distinct from all input ports, and
input relation-table ports to differ from the domain. Full injectivity of
element ports is unnecessary because the atomic routines support repeated
arguments; representation consistency already forces aliased values equal.
All private work stacks start empty. The compiler theorem should quantify
over arbitrary surrounding stack contents and control state and return
`StackBoolean.Returns ... (TableEvaluation.evaluate φ A v η)` with a fixed
polynomial bound. Positivity/admissibility is needed later for semantic
agreement, not to run the finite-round evaluator.

For the existential case, extend element ports with the private coordinate
port. For LFP, extend them with the private tuple-coordinate ports and extend
the relation environment with the private current-table port. A remaining
generic observation lemma is needed for `packTuple`: reading its i-th
coordinate port returns the i-th supplied unary tuple value. The existing
freshness, stack-update, and scratch lemmas handle old input ports and child
workspace; tests have already discharged coordinate reads at fixed arity.

Suitable recursive bounds are 1 for truth, a coarse linear bound for unary
comparison, `StackTableLookup.costPolynomial` for relation atoms, sums for
Boolean composition, `(P + 15) * X + 11` for existential quantification,
and `StackLfpValue.costPolynomial P k` for LFP. These are actual execution
bounds, unlike the older abstract `EvaluationWork` charge.

Two interface details should be handled before the compiler induction:

1. Add a coordinate-observation lemma for `packTuple` specialized to
   `List.ofFn (fun i : Fin k => (counterPort i, coordPort i))` and
   `List.ofFn values`. Under port distinctness, reading `coordPort i` gives
   `replicate (values i) true`. Induct on k and split i with `Fin.cases`;
   the zero case uses `packTuple_fresh` on the tail, and the successor case
   applies the induction hypothesis to the tail store family. The loop's
   remaining-counter list need not be bounded to prove this observation.
2. The current `StackLfpValue.evaluate_returns` expresses semantic arity as
   `tupleSlots.length`. A small wrapper with explicit k and assumptions
   `tupleSlots.length = k` and `powerCounters.length = k` will avoid casts
   when applying it to a raw LFP binder of arity k. Prove that wrapper by
   substituting k using the first equality and applying the existing theorem.
   Keep tupleSlots an independent list parameter in the wrapper statement;
   this makes the substitution straightforward. No concept change is needed.

## General formula compiler completed

The preceding compiler plan is now implemented. `FormulaProgram.compile`
constructs a fixed actual stack program from raw syntax and port maps.
`Work φ` has explicit recursive Fintype and DecidableEq instances; the
compiler contains no structure, domain size, or semantic evaluator parameter.
`FormulaRepresentation` connects unary element stacks and dense relation
tables to the semantic environments, with framing and binder-extension
lemmas. Element ports may alias; private work ports must be injective and
fresh from inputs. `TupleCoordinates.coordinate_ofFn`, `StackLfpArity`,
and `LfpWorkspace` provide the binder interface and private-port geometry.

`FormulaProgram.compile_correct` in `FormulaLfpCorrectness.lean` is proved
by structural induction for EVERY raw formula, including arbitrary nested
LFP and existential binders. It gives an actual `StackBoolean.Returns`
execution bounded by `(costPolynomial φ).eval A.size`, preserving every
stack and the outer auxiliary control state. No admissibility assumption
is needed for finite-round evaluation; the existing semantic correctness
theorem supplies the LFP interpretation for admissible formulas. The
compiler theorem and LFP case use only standard Lean axioms.

This completes the general compiler induction, but not `evaluationInP`.
The next step is decoder/evaluator/output composition:

1. Use ambient ports `FiniteDecoder.Port σ m ⊕ Work φ` and embed the
   decoder with `StackRename.executes_in_sum`, leaving all evaluator work
   empty. `FiniteDecoder.program_executes` gives its structured execution.
2. Strengthen the decoder interface from coordinate LENGTH to the actual
   unary coordinate word. `DecoderCorrectness.Represents.coords` currently
   only supplies the length. `StackCheckedUnary.result` prepends true tokens
   to the initially empty coordinate; `StackCheckBound.result` preserves
   stacks, and later coordinate parses preserve earlier coordinate ports.
   Prove this through `StackReadCoordinates.result`, then combine with
   `DecoderCorrectness.result_represents`. Input tables/domain are already
   in the exact required representation. No concept change is needed.
3. Branch on decoder validity, run the compiler on valid inputs, and return
   false on malformed input. `DecoderAgreement.accepts_iff_encoding` and
   exact decoding agreement provide the semantic link. Work ports are the
   right summand; input ports are the left summand and statically distinct.
4. Clear every finite stack port, retain the Boolean in control, put its
   singleton output on the designated output stack, and reset finite control
   to the machine's initial value. A simple coarse bound avoids finite sums:
   prove by induction on `Executes` that EACH stack length grows by at most
   the execution cost. Thus each decoded stack has length at most
   `M = input length + decoder cost`, even on malformed input. The evaluator
   restores all stacks. Clear a fixed list of all ports at cost at most
   `(2*M + 2) * number of ports + 1`; `StackClear.clear_store` preserves
   auxiliary control and resets scratch, so the answer survives. Finish
   with a push of `state.1.2` onto the output and a load of the initial
   control. The finite port count is a formula-dependent constant.
5. Bound the valid domain size by input length (`InputSize`), use polynomial
   evaluation monotonicity, and apply `StackProgram.program_polytime` to
   produce the exact required `TM2ComputableInPolyTime` instance. Do not use
   mathlib's unproved composition assertion.

The reverse arbitrary-TM2 simulation remains open. Both main concept axioms
and the authorized final submission remain pending.

Validation for this checkpoint: `tests/FormulaMachine.lean` passes actual
compiled TM2 runs for forward/backward/reflexive directed reachability,
an inner LFP reading the outer relation while retaining free parameters,
empty existential quantification, empty-domain nullary relation bits, and
nested nullary fixed points. Every run checks all stack contents after
return, including a populated unrelated stack. A symbolic instantiation
uses `compile_correct` at arbitrary ambient port and auxiliary-state types.
The audited compiler/LFP theorems use only propext, Classical.choice, and
Quot.sound; coordinate observation uses only propext and Quot.sound.
Full `env LEAN_NUM_THREADS=2 lax build . --replay --no-color` passed in
9m35s (kernel replay 9m06s), including all seven new modules. Concepts remain
identical to cf16245. Lax reports eight concepts and seven annotated proofs;
the two main computational axioms remain open. Nothing was submitted.

## Forward computational theorem completed

The decoder/evaluator/output assembly is now proved, superseding the
remaining-forward-work plans above:

- `DecoderUnary.finite_coord` proves the exact retained unary coordinate
  words, completing the decoder-to-evaluator representation interface.
- `StackOutput.length_executes` bounds each stack's length by its original
  length plus execution cost, for arbitrary structured programs and alphabets.
  `clearPorts_executes` clears a fixed list at a coarse linear bound in the
  common maximum stack length; `output_executes` retains the answer, clears
  every port, emits its singleton Boolean, and resets the control state.
- `FormulaPorts` explicitly enumerates decoder and recursively allocated
  formula ports, keeping the entire decision machine executable without a
  noncomputable choice of finite enumeration.
- `FormulaDecision.evaluate_executes` uses the decoder's validity bit to
  select the proved evaluator or false, and its result is exactly the existing
  total `DecisionProcedure.decideFormula` on every bit string.
- `FormulaDecision.program_executes` composes decoder, evaluator, and output
  into the exact input/output stack convention required by mathlib, with a
  polynomial bound in input bit length including all malformed inputs.
  `computableInPolyTime` supplies the actual bundled finite TM2 witness.
- `FixedPointEvaluation.evaluationInP` now has an unconditional annotated
  proof. `VardiImmerman.definable_inP` uses it, and the final equivalence's
  only remaining Lax assumption is `VardiImmerman.ptimeDefinable`.

The approved concepts are unchanged. The reverse arbitrary polynomial-time
TM2-to-FO(LFP) construction and final submission remain unfinished.

The next concrete reverse-direction subtask is finite reachable alphabet
support for an arbitrary `Turing.FinTM2`. Its definition only assumes
`Fintype (Γ k₀)` on the input alphabet; do not silently assume all Γ k finite.
All control states and labels are finite. For each statement q, recursively
collect a finite set of tagged symbols `(k, a) : Sigma Γ`: a push contributes
the image of its finite control-state type under `v ↦ (k, f v)`, ordinary
continuations recurse, branches take a union, and goto/halt contribute empty.
Unite these sets over all machine labels and add every input-alphabet symbol.
Prove by induction on `TM2.stepAux` that every stack symbol stays in this
set, and hence through `TM2.step` and bounded runs. This gives the finite
symbol codes needed by either persistent-node or bounded-cell simulation.

The inspected primary implementation is mathlib's
`Computability/TuringMachine/StackTuringMachine.lean`. `TM2.stepAux` executes
an entire finite statement tree in one machine step; pop/peek can change
control before the continuation. Its existing `stmts₁`/`stmts` collect finite
substatement sets, and `stmts₁_trans` supplies closure under substatements.
These can support finite micro-instruction labels. Existing `SupportsStmt`
tracks goto labels only; it does not prove finite reachable alphabets.
Any microstep simulation must prove its refinement and bound by a fixed
multiple of machine steps. The reverse simulation is not yet implemented.

Forward-checkpoint validation: `tests/DecisionMachine.lean` passes actual
complete machines starting from mathlib's `initList`, including directed
reachability in both directions and on the diagonal, empty-domain truth and
existential quantification, nullary relation/LFP queries, truncated and
trailing encodings, and all Boolean words of lengths 0–5 for two signatures.
Each run checks halting, exactly one output bit, every other stack empty,
and the full finite control reset. The forward theorem, its bundled machine
witness, and `definable_inP` use only standard Lean axioms. The final
equivalence's audit reports exactly one additional axiom: `ptimeDefinable`.
Full `env LEAN_NUM_THREADS=2 lax build . --replay --no-color` passed in
9m13s (kernel replay 8m48s): eight concepts and eight annotated proofs.
Concepts remain identical to cf16245. Nothing was submitted.

## Finite alphabets and operation-by-operation TM2 simulation

The first reverse-direction normalization is now implemented:

- `TM2Alphabet.symbols` collects all possible push symbols from a statement
  over its finite control state. `alphabet tm` adds these across all labels
  and includes the input alphabet. Its membership invariant is proved through
  every statement operation, macro-step, and bounded actual TM2 run. No
  finiteness assumption is added for internal alphabet types. `Symbol tm`
  is a finite type of tagged reachable symbols.
- `TM2Micro.next` splits each TM2 statement into individual push, pop, peek,
  load, branch, goto, and halt operations, with explicit label boundaries.
  `statement_refines` proves agreement with the actual `TM2.stepAux`.
  `evals_refines` lifts an `EvalsToInTime` witness to the new simulation with
  a fixed multiplicative time overhead `factor tm`. The factor is a coarse
  sum of statement weights plus one; no optimized bound is needed.
- `TM2Micro.evals_at_time` gives the same terminal configuration at every
  time beyond that bound, using an absorbing halt boundary. This is suitable
  for a tuple-sized time horizon in the eventual fixed-point formula.
- `TM2MicroSupport.controls` is a finite set of boundary labels and
  substatement cursors. `initial_run_support` proves that every intermediate
  control and stack symbol stays in the corresponding finite support sets.
  `initial_length` bounds each stack by input length plus the number of
  individual operations, so stack-address space is also polynomial.

These normalize arbitrary finite TM2 machines without weakening the approved
complexity definition. They do not yet construct the reverse FO(LFP) formula.
The next task is to encode the normalized computation by positive relational
rules, prove their soundness/completeness, and interpret the chosen input
encoding and finite tags by actual formulas. The existing persistent-node
candidate avoids first-order arithmetic for flat input bit offsets: initial
nodes are tagged by encoding block and local tuple/element address, and each
push node is tagged by its unique microstep time. The new microstep model
makes at most one push per time, so no within-statement position tag is needed
for created nodes. Pop/peek use positive node facts; all pointed runs can be
kept separate by prefixing facts with the query tuple. This remains a planned
construction, not an assumed simulation correspondence.

A suitable next bounded implementation is a persistent-stack representation
lemma independent of formula syntax: represent a stack by an optional node
head and a finite chain of immutable `(node, symbol, parent)` records. Under
functional node records, prove uniqueness of the represented list and exact
push/pop/peek behavior; adding a fresh node preserves all existing chains.
Then lift this representation to `TM2Micro.next`, using one fresh created
node keyed by the current microstep for a push and preserving old records.
Initial chains can first use a list of abstract node identifiers in input
order; the subsequent FO input interpretation will supply their concrete
block/tuple encoding. Do not require a flat arithmetic bit-address formula
or silently assume a rule-to-machine correspondence.

Validation: `tests/TM2Micro.lean` passes a concrete two-stack TM2 with Bool
input and an infinite Nat internal alphabet, using push, pop, peek, load,
branch, goto, and halt. It checks intermediate symbols, final stack contents,
different termination times for the two branches, and stability after halt.
Symbolic examples instantiate the general support and refinement theorems.
All five audited theorem sets contain only standard Lean axioms. Full
`env LEAN_NUM_THREADS=2 lax build . --replay --no-color` passed in 11m18s
(kernel replay 11m07s): eight concepts and eight annotated proofs. The
approved concepts remain identical to cf16245. The forward theorem is proved;
the reverse theorem and final submission remain pending.
