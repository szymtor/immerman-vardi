# Registered final submission — lax-751879

Updated 2026-09-16. The user authorized final publication of the six current
Lean 4.33 submissions and normalization of AI author credits to GPT, retaining
version numbers. This supersedes earlier keep-draft restrictions for this release.

- Registered and citable: https://laxarchive.org/lax-751879/
- Frozen source: `9fa09900c827396420a8bcfd22bc624e5c980a53` on `lean-4.33`.
- The release changes only `manifest.yaml` relative to the previous accepted
  Archive source; Lean sources and the previously replayed proofs are unchanged.
- Fresh full local Lax compilation and statement inspection passed. The Archive
  independently verified the author-only diff and reused its validated capture.
- After registration, the refreshed Archive record was verified against the
  exact source and capture provenance, GPT author credits, all concept source
  text, proof counts and complete proof closure, and registered dependency pins.
- Evidence: `../migration-tools/finalize-foundations-verification.log` and
  the corresponding `finalize-*-build.log`, `-submit.log`, and `-register.log`.

No further publication is needed. Downstream submissions must pin the frozen
source above. Local status documentation may advance after that immutable commit.

## Earlier history

# Lean 4.33 draft migration

Original draft: lax-979537. New local draft: lax-751879.
User authorized a separate draft with a link to the original, without supersedes.
Sources are copied from the original published commit; namespaces, toolchain,
mathlib and dependency names have been updated. Dependency commit pins for
other new drafts are pending their validation and publication. Full Lean 4.33 validation and independent kernel replay passed (2m39s;
8 concepts, 9 annotated proofs). CapturesPtime regression passed, including
concrete node/clock examples and background-only axiom audits.
Published at https://laxarchive.org/lax-751879/ from
22b06ecb75e26570ccfb67582c9e3d12e88fdf65 (issue 110). Archive rebuild
passed in 6m26s and publication succeeded. No registration performed.

Compatibility changes: explicit simpa using!, dependent-index elaboration
compatibility options in affected proof modules, and explicit simplification
of set membership, Nat successors and list lengths. Concept code is unchanged
apart from namespace renaming. Retain inherited helper lemmas intentionally
for downstream reuse (including Fagin) and provenance; the new linter reports
184 unused-helper warnings, some on generated declarations.

Next: Fagin port pins this published commit.

## Historical record from the original (not validation of this port)

# Immerman–Vardi proof implementation

Updated: 2026-09-08.

## Current result

Both directions and `ImmermanVardi.capturesPtime` are proved without
outstanding Lax assumptions. The initialized positive rule system defines
exactly the encoded machine computation; the acceptance formula and finite
exception construction finish the reverse implication. All nine annotated
proofs passed the full Lax build and kernel replay (6m55s overall, 6m48s
replay). The final regression test passed, and the main theorems depend only
on `propext`, `Classical.choice`, and `Quot.sound`.

The user requested the name Immerman–Vardi, including the abstract and
comments. The project directory is now `immerman-vardi`; the theorem modules
and namespaces are `ImmermanVardi`. Concept statements are unchanged apart
from this mechanical rename. The renamed Lax build passed (37s), and the
renamed final regression test and axiom audit passed. Archive submission
remains to be completed. The local archive ID is `lax-751879`; the current CLI
reserves this six-digit ID on first submission, independently of its issue
number. The source repository is https://github.com/szymtor/immerman-vardi.

## Earlier implementation log

The entries below record historical checkpoints; their open obligations have
been discharged by the current result above.

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
Lax560851 was considered but is not a concept or proof dependency. The user's
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

`ImmermanVardi.capturesPtime` has an annotated proof relative to precisely
`ImmermanVardi.ptimeDefinable`; its forward direction uses the proved evaluator.
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

1. `ImmermanVardi.ptimeDefinable`: construct a positive fixed-point formula
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
ready-made compiler for the relation-table evaluator. Lax759944 has substantial
RAM/TM simulation proofs, and Lax865980Proofs has an IMP compiler, which may help
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

Provisional id: lax-751879. No remote is configured, authors remain unfilled,
and nothing has been submitted or published. Do not publish this as a completed
Immerman–Vardi formalization while the reverse computational direction is open.
The preview uses http://localhost:8125/lax-751879/index.html when running.

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
  proof. `ImmermanVardi.definable_inP` uses it, and the final equivalence's
  only remaining Lax assumption is `ImmermanVardi.ptimeDefinable`.

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

## Persistent-node simulation and exact positive closure

The planned linked-stack simulation is now implemented and connected to
arbitrary actual TM2 runs:

- `PersistentStack` represents a list by a finite chain of immutable
  `(node, symbol, parent)` records. Functional records imply a unique list
  at each head; different heads may share a suffix. Fresh insertion preserves
  functionality and all old chains. `Read` uses an explicit empty head or
  one positive node fact, with proved lookup correctness and uniqueness.
- `NodeMachine.Step` implements every `TM2Micro.next` operation using heads
  and tagged symbol records. `step_sound` preserves representation and
  functionality when a newly allocated node is fresh, and `step_exists`
  proves totality on represented stacks. Steps are deterministic under a
  functional heap and monotone when more node facts are available.
- `TimedNodes.Run` allocates push nodes as `Sum.inr time`, separating them
  from `Sum.inl initialIdentifier`. The timestamp invariant proves freshness
  for each step. `run_sound`, `run_exists`, and `run_unique` give exact
  agreement with the normalized TM2 at every time.
- `NodeInput` explicitly builds initial node records from the input list
  and any injective identifier map `Fin input.length → Initial`. It proves
  the initial chain, functionality, timestamp bound, and exact representation
  of `Turing.initList`. Thus these initial invariants are discharged, not
  assumptions of the reverse computational theorem.
- `NodeTrace` chooses a proof-side canonical run, proves its adjacent steps,
  and proves monotonicity of its heap. Its `Context` stores only the initial
  representation data; `NodeTrace.input` supplies this context for actual
  TM2 inputs using the preceding theorems.
- `NodeClosure.operator` is a concrete monotone operator on configuration
  and node facts. Initial nodes/configuration seed the relation; configuration
  facts produce push records and next configurations using positive reads.
  `closure_eq_trace` proves that its least fixed point is EXACTLY the bounded
  run's configurations and final heap, with no spurious facts. Soundness uses
  the final functional heap and deterministic steps; completeness lifts each
  actual step through the growing node facts.
- `NodeAcceptance.accepts_iff` connects this positive closure to the actual
  output symbol of any bounded TM2 computation. Any horizon at least
  `TM2Micro.factor tm * timeBound` is sufficient because halt is absorbing.

This completes the semantic positive-rule simulation. It does not yet prove
`ptimeDefinable`: the concrete rule operator still must be represented by
actual FO(LFP) syntax over the input structure. Remaining work includes the
FO interpretation of initial identifiers and symbols for the chosen dense
encoding, finite tag and tuple coding, query-parameter separation, and the
coarse polynomial time/address horizon with small-domain patching.

The next syntax bridge must expand the finite cases of `NodeMachine.Step`
into actual `PositiveRules.Rule` values. In `NodeClosure.operator`, the
existential result heap of a step is merely a convenient semantic projection;
it is NOT a first-order quantifier. Eliminate it by the explicit Step cases:
push/load/branch/goto/halt have fixed head/control updates, and pop/peek use
one `Read` fact with a typed finite symbol choice. No negative node-freshness
test is needed in the logical rules; freshness is already proved by time.
Use the proved finite support sets from `TM2MicroSupport`/`TM2Alphabet`, and
instantiate initial identifiers by block/local tuple coordinates. The raw
semantic Fact type is unrestricted, so any finite tuple presentation must
prove its support/coding correspondence, not assume global expressibility.

Concrete next input-interpretation option: split the approved encoding into
a fixed list of segments. The header is a unary-ones segment followed by a
nullary false delimiter; each input relation is a full canonical tuple-table
segment; each pointed coordinate is a unary-ones segment restricted by
`i < a_j`, followed by its nullary false delimiter. Give every segment its
own finite tag and pad local tuple addresses by zero to one fixed width.
For n above the fixed tag threshold, these are actual tuples in Fin n.
This makes symbol and valid-position predicates first-order. Within-segment
successors use ordinary/lexicographic successor; across segments, a fixed
finite disjunction requires the previous last position, the next first
position, and emptiness of every intervening segment. Only pointed unary
segments can be empty for n ≥ 2. Prove the concatenated segment enumeration
is duplicate-free and its bit list equals `StructureEncoding.encode A`;
its position map then instantiates the injective `ids` parameter already
used by NodeInput/NodeAcceptance. Small domains remain covered by the proved
finite-exception construction. This is a next implementation plan, not a
proved input interpretation yet.

Validation: `tests/NodeSimulation.lean` passed the persistent-stack sharing,
positive-read, and actual constant-output TM2 examples, including symbolic
acceptance at every sufficient horizon. Axiom audits contain only standard
Lean axioms. Full `env LEAN_NUM_THREADS=2 lax build . --replay --no-color`
passed in 10m39s (kernel replay 10m22s), with eight concepts and eight
annotated proofs. Concepts remain unchanged from cf16245. The reverse
definability theorem and final submission are still pending.

## Concrete first-order input positions and bits

The segment plan now has actual Lean definitions and actual FO syntax:

- `InputSegments.Segment` distinguishes the size header, header delimiter,
  each relation table, each query-coordinate unary block, and its delimiter.
  Segment arities are fixed by the vocabulary/query arity. Local enumerations
  use precisely the approved lexicographic tuple tables and unary blocks.
  `word_eq_encode` proves equality with the frozen concept encoding, including
  empty universes and nullary relations. `positions_nodup`, `ids_injective`,
  and `ids_bit` provide distinct initial identifiers and their exact bit values
  for every input-list index. These identifiers fit the existing NodeInput API.
- `InputSegmentFormulas.valid` and `.symbol` are actual first-order formulas,
  with semantic correctness: local membership is unrestricted except for
  coordinate blocks, and symbols are true/false or the relevant relation atom.
- `InputTupleCodes` gives every segment a distinct fixed numeral tag and
  pads its coordinates with zeros. `width σ = σ.sum + 1` suffices for all
  local arities. For domain size at least `2 + σ.length + 2*m`, `code` is
  injective into tuples of length `width σ + 1`. `presentation` uses actual
  numeral, validity, and padding formulas; its semantics is proved.
- `InputPositionFormulas.eval_position` proves that a finite disjunction of
  segment presentations defines exactly the tuple codes of input positions.
  `InputBitFormulas.eval_hasBit` proves that its labeled version defines
  exactly the positions carrying either specified bit. Both are first-order,
  uniformly in all structure sizes above the fixed tag threshold. No flat
  address arithmetic is an expressibility assumption.

These modules compile. The next missing input component is the parent-link
interpretation: first position, consecutive positions, and last position
must be recognized by actual formulas and connected to NodeInput.records.
A direct option is to prove the coded position list strictly lexicographically
increasing: segment tags increase, and each local enumeration increases in
tuple order. Then first/last/successor are the usual order predicates
restricted by the already proved `position` formula. Unlike raw tuple
successor, restricted successor skips unused tags, padding gaps, empty
coordinate segments, and zero-sized relation tables. Prove its correspondence
with adjacent list indices before using it as a stack parent relation.
This ordering/link interpretation is not yet implemented. Finite transition
rules, query-prefix isolation, polynomial horizons, and the reverse theorem
also remain pending; the submission is not ready.

Validation: `tests/InputInterpretation.lean` passes exact-word examples for
a mixed nullary/unary vocabulary, empty and maximal unary query blocks, and
an empty universe, plus symbolic identifier/bit and actual-formula checks.
All six audited theorem sets contain only standard Lean axioms. The five
modules and their dependencies compile. Full
`env LEAN_NUM_THREADS=2 lax build . --replay --no-color` passed in 15m03s
(kernel replay 13m37s), with eight concepts and eight annotated proofs.
The approved concept files remain identical to cf16245.

Integration detail checked in mathlib: the polynomial-time witness stores
`inputAlphabet : tm.Γ tm.k₀ ≃ Bool` and the actual input is
`(encode A).map inputAlphabet.invFun`. Its length equals the bit-word length;
transport `InputSegments.ids` across that length equality and label initial
records by the inverse alphabet image of the proved bit. Likewise the
accepting output symbol is `outputAlphabet.invFun true`. Do not assume the
machine's alphabet types are definitionally Bool.

## Input-stack links and a polynomial tuple-clock horizon

The next initial-graph obligations are now implemented:

- `InputOrder` proves that canonical relation tuples and segment-local
  enumerations increase lexicographically, that segment tags increase, and
  that the whole padded position-code list is strictly increasing. Numerical
  tuple-address ranks inherit this order (`rank_sorted`).
- `SortedLinks` defines first, last, and restricted successor on a finite
  ranked list. Under strict ordering, these predicates are exactly index zero,
  the final index, and adjacent indices. Thus the restricted order correctly
  skips empty segments and unused/padded tuple codes.
- `InputLinkFormulas` constructs actual first-order first/last/successor
  formulas. Its `window` quantifier ranges over valid input positions and
  optional strict tuple bounds. Both coded-position and arbitrary-assignment
  correctness theorems are proved; no order/link expressibility assumption
  remains at this interface.
- `OrderedRecords.records_iff` proves that the immutable records for a list
  have exactly its labels and order-defined optional parents. `head_iff`
  identifies the first position as the head. `RenameRecords` proves that
  renaming node identifiers maps keys and optional parents in those records.
- `InitialInput` instantiates the graph for an arbitrary bundled TM2 with
  `inputAlphabet : tm.Γ tm.k₀ ≃ Bool`. It labels each position by the inverse
  alphabet image of its bit, proves the exact list is the approved encoding
  mapped through that inverse, and supplies injective names to NodeInput.
  `heap_iff` and `head_iff` connect the actual initialized heap/head with the
  proved position, label, first, and parent relations. `represented_run`
  connects this concrete graph to the original machine input at every step.
- `SimulationHorizon.exists_horizon` composes the approved encoding-length
  polynomial with an arbitrary runtime polynomial and absorbs microstep
  overhead into a single power. It proves
  `TM2Micro.factor tm * time.eval (encode A).length ≤ n^d - 1` for every
  pointed input with `n ≥ 2`. No precise exponent or runtime estimate is
  required. `exists_deciding_horizon` applies this to any actual
  `TM2ComputableInPolyTime id (fun b => [b]) f` witness and proves that its
  concrete positive node closure accepts exactly the output bit `f (encode A)`.

The input interpretation and semantic polynomial-time simulation are now
connected. The reverse theorem is STILL NOT proved: the finite supported
control/state/symbol cases and bounded node/time addresses must be encoded
into fixed-arity facts, and actual positive transition rules must be supplied
with correctness. Query-prefix isolation (or an explicitly parameterized
rule compiler) and the existing small-domain patch must then be integrated.
Do not count `exists_deciding_horizon` as FO(LFP) definability: it concerns
the concrete semantic closure, whose remaining rule presentation is explicit
in its documentation. The final theorem still has its one reverse assumption.

All seven new proof modules compile. The extended `tests/InputInterpretation.lean`
regression passed, including adjacent/nonadjacent positions across an empty
coordinate block, endpoints, and the uniform actual-formula/adjacent-index
equivalence. All fourteen audited theorem sets contain only standard Lean
axioms. The approved concepts are unchanged from cf16245; `git diff --check`
passes. Full `env LEAN_NUM_THREADS=2 lax build . --replay --no-color` passed
in 16m48s (kernel replay 15m53s), with eight concepts and eight annotated
proofs. Both replay session 28192 and test session 68188 finished successfully.

Concrete next finite-coding obligations identified from the current sources:
`TM2MicroSupport.initial_run_support` gives finite control and live-stack
alphabet support. To code the accumulated heap, also prove finite symbol
support for old/popped records, by induction using `NodeMachine.step_records`:
old records retain their support and a new push symbol is in the proved
machine alphabet. Prove that every nonempty record parent is an existing
node key; the initial list has this property and fresh pushes point to an
already represented head. `TimedNodes.Bounded` then bounds parent/head time
names as well as keys. This supplies the support and boundedness needed for
injective codes of the entire canonical trace, not just its currently live
stacks. Initial identifiers already have their proved injective tuple code.
Do not assume an injective code for arbitrary unbounded raw Fact values.

Compiler interface choice for the next step: use the free element parameters
already supported by the approved LFP constructor. A parameterized rule can
extend `PositiveRules.Rule σ k` with a map selecting the query variables from
its witness assignment. Its actual matrix additionally equates those selected
variables with the free query tuple; its head and premises remain k-ary facts.
The resulting body has k bound tuple variables plus m free query variables.
Prove the resulting membership formula's body operator equals the rule
operator at that fixed query valuation. This avoids carrying the query tuple
inside every fact and proving a separate all-query prefix-isolation theorem.
It changes only the proof compiler, not the approved concepts. This interface
extension is now implemented as described below.

## Finite fact coding and parameterized rule compiler (working tree)

Nine additional proof modules compile: `ParameterizedRules`,
`RuleConstants`, `NodeSupport`, `TupleCoding`, `SupportedCodes`, `NodeCodes`,
`FactSupport`, `FactCodes`, and `TraceCodes`. They are now imported into
the root proof module along with the six concrete-rule modules below.

`ParameterizedRules.eval_membership` proves that the actual LFP formula
denotes the positive rule closure at a fixed free query valuation.
`RuleConstants.compile_holds` proves correctness of numeral bindings in
rule templates. Thus query-prefix isolation is no longer needed.

The support proofs cover retained heap records and their parents as well as
live heads. The coding proofs supply injective fixed-arity tuple codes for
supported configurations and records within the tuple-clock bound.
`TraceCodes` instantiates these codes for actual polynomial-time machine
witnesses and the approved input representation. Its closure encoding and
membership equivalence concern the semantic closure; they do not yet give
the concrete finite transition rule list or its syntactic correctness.

The parameterized-rule and finite-fact-code regressions passed. The seven theorem axiom audits in
`tests/FiniteFactCodes.lean` report only `propext`, `Classical.choice`, and
`Quot.sound`. The approved concepts remain unchanged, and the final theorem
still explicitly assumes `ImmermanVardi.ptimeDefinable`.

Next: construct concrete initialization and transition rules, prove their
LFP matches the encoded canonical trace, extract acceptance, and integrate
the existing small-domain patch. Then discharge the reverse assumption,
complete validation, and submit. No submission has been made.

## Concrete stack-preserving rules

`FactPatterns` proves that variable-pattern assignment commutes with the
actual configuration and record tuple layouts. `MachineConstants` supplies
a fixed numeral block for all machine tags, supported controls/symbols, and
finite internal states. `ControlRules.transition` is an actual positive rule
template with query variables, two clock blocks, and shared head variables.
Its first-order guard requires consecutive tuple addresses.
`transition_holds` proves its exact interpretation for arbitrary relation
premises, including all existential witnesses.

`PlainControl.target` handles stopped, enter, load, branch, goto, and halt.
`target_step` proves that each case is an actual `NodeMachine.Step` for any
heap and head assignment. `rules` enumerates these cases over the proved
finite controls and internal states; `operator_iff` proves the exact
interpretation of that finite concrete rule list.

`ControlValues` decodes a configuration pattern against a supported encoded
fact and rules out node/configuration tag collisions. `PlainClosure.preserves`
proves that the concrete rules preserve `TraceCodes.encoded` for every actual
polynomial-time machine witness and every sufficiently large pointed input.
`PlainClosure.derives` proves that each supported stack-preserving transition
before the final clock value is derived from its encoded source fact. These
are concrete syntax-to-trace results, not a definability assumption.

All fifteen new modules compile and are integrated into the proof root.
`env LEAN_NUM_THREADS=2 lax build . --no-color` passed in 26s, reporting eight
concepts and eight annotated proofs. The final annotated equivalence still
retains its sole reverse assumption. A targeted kernel replay of all fifteen
new modules passed (session 82371, exit 0); this checks every new module's
declarations against its imports, and is not a new full-root replay. The
previous full replay is the successful 7175e4e checkpoint. All validation
processes for this checkpoint are terminal. Passing regression checks cover literal rule constants, branch
outcomes and state updates, separation of push from plain rules, and failure
of the actual transition guard to wrap the final clock back to zero.

The next concrete rule families are push (next configuration plus an emitted
node record), pop/peek (empty and positive-record cases), and initialization
(input-bit/link formulas and the first input head). Then combine the families,
prove equality of their LFP with the encoded canonical trace, extract
acceptance, and apply `FiniteExceptions.definable_of_above`. The theorem and
submission remain incomplete.

`HeadPatterns` is also implemented and has passed elaboration and kernel replay.
It selects and updates one flattened stack-head row, proves that assignment
commutes with that update, identifies it with `FactCodes.heads` of a machine
head update, and identifies the fresh-node pattern with the code of the
source-time node. It has been added to the proof root. The final full project
build passed in 24s (session 95099), its targeted kernel replay passed
(session 58550), and the expanded control/head-pattern regression and nine
axiom audits passed (session 89937). All sixteen new modules are therefore
integrated and individually kernel-replayed; no claim of a fresh full-root
replay is made. No validation process remains running.

For push, reuse `ControlRules`' query/before/after/head data layout and source
configuration pattern. Enumerate supported controls and finite states as in
`PlainControl.rules`. A push effect contains its stack key, typed pushed
symbol, and successor instruction. Generate two rules per effect: a next
configuration with `HeadPatterns.update` at that key using `fresh` on the
source clock, and a node fact whose parent is `HeadPatterns.get` of the old
head. Both rules have the same source-configuration premise and successor
guard. `map_update`, `get_heads`, `update_heads`, and `fresh_code` supply the
assignment/semantic equalities needed for the two head interpretations.
Prove soundness via the actual push constructor and `NodeClosure.closure_fixed`,
following `PlainClosure.preserves`; derive both heads following `derives`.

## All concrete transition rules and trace derivation (working tree)

The push/read construction above is now implemented. Twenty new modules
compile and are imported into the proof root:

- `PushEffects`, `PushPatterns`, `PushRules`, `PushValues`, and `PushClosure`
  construct the two push conclusions and prove their exact rule
  interpretation, encoded-trace preservation, and bounded-step derivation.
- `ReadEffects` proves the actual pop/peek transitions. `ReadSymbols` derives
  a finite enumeration for each stack's supported symbols without requiring
  its alphabet type to be finite.
- `EmptyHead`, `EmptyReadRules`, and `EmptyReadClosure` compile the all-zero
  empty-head guard and prove soundness and derivation for empty pop/peek.
- `RuleExtension`, `ReadPatterns`, and `NonemptyPatterns` supply one parent
  tuple and the configuration/node patterns for a nonempty read.
  `ReadRecordValues` decodes an encoded node premise's key, symbol, and
  parent and excludes configuration/node tag collisions.
- `NonemptyReadRules` enumerates supported symbols and requires both a
  source configuration and a positive node-record premise.
  `NonemptyReadClosure` proves preservation and derivation for both nonempty
  pop and peek, including the actual head update for pop.
- `TransitionRules` combines all five lists: plain, push-configuration,
  push-record, empty-read, and nonempty-read. `preserves` proves their whole
  operator preserves the actual encoded trace.
- `ReadDerivation` handles either read shape. `TransitionDerivation.step`
  proves every bounded `NodeMachine.Step` is derived from its configuration
  and heap premises. `added` derives every emitted node record.
- `TransitionClosure.at_time` proves, by induction on canonical snapshots,
  that a relation closed under these concrete transition rules and containing
  the initial configuration and records contains every bounded snapshot and
  heap. `encoded_subset` gives containment of the whole encoded trace.

The seed hypotheses in `TransitionClosure` are ordinary closure-principle
hypotheses. They are NOT a completed initialization compiler or an assumption
to use in the final theorem. Concrete initialization rules must still prove
them for the actual LFP. The final theorem retains its reverse assumption;
the submission is not ready.

The project build passed in 7s (session 3454). The new transition regression
passed (session 83702), checking two distinct pushed Nat values in an infinite
internal alphabet, pop versus peek and preservation of other stack heads,
and impossibility of a nonempty read when the relation has configuration-tagged
facts only. All seventeen audited theorem sets use only standard Lean axioms.
Approved concepts remain unchanged from cf16245, and `git diff --check` passes.
A targeted kernel replay of all twenty new modules passed (session 65438,
exit 0). Each new module's declarations were replayed against its imports;
this is not a fresh full-root replay. The previous complete replay remains
7175e4e, and the preceding sixteen-module checkpoint was individually
replayed at 8874a8f. All validation processes for this checkpoint are terminal.

Next implement five initialization templates: one configuration rule guarded
by first clock and first input position, and four node rules (bit false/true
times successor-parent/final-empty-parent). `InputBitFormulas.eval_hasBit`,
`InputLinkFormulas.eval_first/next/last`, and `InitialInput.heap_iff/head_iff`
already give their semantic interfaces. The input-position code has width
`InputTupleCodes.width σ + 1`; `HeadPatterns.fresh zero one position` can
represent an initial node by using tag one rather than the time-node tag two.
The record symbol is `Sigma.mk tm.k₀ (inputAlphabet.symm bit)`.

For the initial configuration, use an existential clock tuple guarded by
`AddressFormulas.first`; its address is zero, so `ControlValues.clock_of_address`
identifies it with `TupleCoding.clock 0`. This avoids a separate all-zero-clock
arithmetic lemma. The stack heads are all empty except `tm.k₀`, whose head is
the first input node. The position list is always nonempty (its header-end
segment supplies a position, even at size zero); `SortedLinks.first_iff` at
index zero can supply the needed first position. After proving initialization
soundness and seed membership, combine its rules with `TransitionRules`, use
`TransitionClosure.encoded_subset` and leastness to prove exact LFP equality,
define output acceptance, and apply the existing small-domain patch.
