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
