# Proof implementation plan

The user authorized proof implementation and completion on 2026-09-08.
The approved concept statements remain unchanged; the user subsequently
requested the mechanical rename to Immerman–Vardi.

Steps 1–6 and the proof, axiom audit, and full kernel replay portions of step 7
are complete. The main equivalence has no outstanding Lax assumptions.
The renamed package build and regression test also pass. Completing archive
submission remains.
The checkpoint entries below are a historical implementation log.

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

## Concrete machine bridge

`StackProgram` now implements the direct compiler route: structured programs
over TM2 push/pop/peek/load, sequence, branch, and while. The compiled label
type is finite by recursion on the syntax tree. `compile_correct` is proved
by induction on terminating executions, and `program_polytime` transfers
polynomial execution bounds to the exact `TM2ComputableInPolyTime` interface.
It requires the actual input/output convention, reset control, and empty work
stacks. It does not assume mathlib's missing machine-composition theorem.

`StackTransfer.transfer_executes` moves bits while preserving auxiliary
control and unrelated stacks. `reverse_polytime` exercises the full compiler
and polynomial-time interface. `StackUnary.parse_executes` parses the size
header into a unary counter, preserves the remaining input, and distinguishes
a delimiter from exhaustion; `splitUnary_correct` links it to the existing
decoder. These routines are actual compiled stack programs.

`StackCopy` now implements source-preserving copy through one temporary
stack, including a store-level framing interface. `StackRepeat` implements
counter-controlled iteration, with a general invariant and a bound on actual
compiled body executions. `StackClear` provides cleanup. `StackCompare`
compares counter lengths, cleans both counters, and leaves a Boolean result;
`StackLookup` consumes an index and returns a table bit or exhaustion.
`StackPower` uses nested copied counters to generate n^k tokens, with a
polynomial depending only on k and all temporary counters returned empty.
These proofs cover arbitrary surrounding stack contents and auxiliary state.

`StackTake`, `StackReadTable`, and `StackReadRelations` now parse every dense
table using the power routine, with checked exhaustion and shared work stacks.
`StackCheckedUnary`, `StackCheckBound`, and `StackCoordinate` handle checked
unary parsing, preserving comparisons, pointed coordinates, and trailing
input. Assemble these into a finite-layout decoder and prove its exact
correspondence with the existing semantic decoder next. See `CURRENT_STATE.md`
for the compatible control-state convention and port reuse.

The full finite decoder is now proved correct in `DecoderCorrectness`.
`decoder_correct` combines a polynomial actual-TM2 execution bound, exact
canonical-input recognition, and the `Represents` contract for retained data.
`DecoderSoundness` removes the redundant serialization pass, and
`RawDecoding`/`DecoderAgreement` establish general machine/semantic-parser
correspondence. These are proofs for every input, not only executable tests.
Continue with the generalized formula evaluator and its concrete machine bound.

Store domain/tuple coordinates as unary
counters on separate stacks, and relations as dense bit tables. This avoids
word-size simulation work: even full table scans and unary arithmetic cost
only polynomial overhead for fixed arities. Formula recursion chooses a fixed
finite collection of stacks and control bits. Quantifier loops range over n;
LFP loops use k nested n-bounded counters to generate tuples and run n^k
stages. Each stage stores its full new table before advancing. Prove program
invariants and correctness, then transfer coarse polynomial bounds through
`program_polytime`. The full evaluator is still not implemented in this
language.

The first evaluator combinators are now proved: `StackFor` gives an ordered
domain loop with callback semantics and cleanup; `StackBoolean` composes
stack-restoring Boolean evaluators; `StackAtomic` handles unary equality and
order, including aliased input ports; and `StackExists` compiles existential
quantification given a bounded body evaluator. `StackRename` embeds verified
programs into larger layouts while preserving extra stacks at unchanged cost.
Tuple iteration, relation access, materialized LFP evaluation, and the general
formula induction remain. These helpers are not a completed forward theorem.

Tuple traversal and individual table rounds are now implemented.
`StackTuples.forTuples_executes` proves fixed-arity nested iteration with
canonical-order fold semantics and a polynomial execution bound.
`StackMaterialize.materialize_executes` constructs the dense table of a
bounded Boolean evaluator, restoring its reverse buffer and loop workspace.
`StackTableRound.round_executes` retains the old table while constructing the
new one, then replaces it in canonical order and cleans the buffers.
Table access, n^k-stage iteration from the all-false table, and the general
formula compilation proof still remain. The reverse simulation is unchanged.

Bounded materialized LFP iteration is now proved in `StackStages`,
`StackInitialTable`, `StackTableStages`, and `StackLfpTables`: build the
all-false table, run n^k actual table rounds, retain the final table, and
restore all other stacks. `DenseTables` and `StackSemanticRounds` identify
the retained result with the rounds of the existing semantic evaluator.
The recursive body premise is a bounded actual Boolean execution for each
valid tuple in the represented current relation. Table lookup, the general
formula compiler, and final output/cleanup assembly remain for the forward
direction. These results do not close either main concept axiom.

Table access is now proved in `StackHorner`, `StackIndex`, `TupleRank`,
`StackReadBit`, and `StackTableLookup`. Unary Horner addresses select exactly
the canonical tuple's bit, and the complete atomic lookup restores every
input and workspace stack. `StackLfpValue` combines materialized rounds,
final tuple lookup, and deletion of the private relation table into the same
Boolean-return contract as the other formula constructors. All individual
raw-formula constructors now have machine implementations; the general
finite-workspace compiler and its representation/correctness induction are
the next main forward obligation. See the latest section of `CURRENT_STATE.md`
for a recursive finite workspace type and the intended compiler invariant.

That compiler is now complete: `FormulaProgram.compile_correct` proves
bounded actual execution for every raw formula, using a finite workspace
determined by syntax and the represented structure/variable/relation
environment. It covers arbitrary nesting and restores every stack. The
forward assembly is now complete in `FormulaDecision`: exact decoding,
evaluation or rejection, clearing the fixed set of ports, singleton Boolean
output, and reset control, all within a polynomial in input bit length.
`FixedPointEvaluation.evaluationInP` is proved without additional assumptions.
The final equivalence now depends only on the reverse simulation below.

For the reverse direction, assess a direct persistent-stack encoding before
adding a full single-tape simulator. A TM2 configuration can be represented
by time, finite control/label, and one node pointer per stack. Initial input
nodes have FO-defined symbols and successor pointers; each push creates a
node indexed by time and a fixed instruction position, recording its symbol
and previous head. Pop/peek consult these positive node facts. A positive
rule system can then encode intermediate instruction states and successive
configurations. This is an implementation candidate, not a proved bridge;
it still requires finite reachable alphabet support, bounded node addresses,
input interpretation, macro-step refinement, and soundness/completeness of
the closure. It may avoid forcing TM2 into the existing local-cell tableau
helper, whose fixed neighborhood does not directly describe linked stacks.

For the persistent-stack candidate, the initial input nodes can be keyed by
encoding block and local tuple/element coordinates instead of by a flat
numeric bit offset. Unary header nodes, their delimiter, each relation-table
block, and each pointed-coordinate unary block have fixed tags. Successors
inside a table use the existing FO tuple successor; successors across block
boundaries use the next block's first node. Unary coordinate bits are guarded
by x < a_i. Nullary table blocks have one node. Pad local coordinates with
zeros to a common fixed arity. Fixed tags and any required padding constants
are available above a fixed domain threshold, with smaller domains handled
by the proved finite-exception theorem. This would avoid implementing FO
arithmetic for the variable sums of block lengths. It remains a construction
plan, not a proved input-interpretation lemma.

The existing parameter-free positive-rule compiler can also be used without
changing its interface: include the pointed query tuple as a prefix of every
fact, and repeat that prefix in every head and premise. The closure then
computes all pointed runs simultaneously, and the final formula tests the
acceptance fact with its free tuple as that prefix. Proving that facts never
mix different prefixes is part of the simulation invariant. Node keys can
distinguish initial nodes from push nodes, whose remaining key is the time
tuple and a fixed instruction-position tag. None of these choices changes
the approved theorem or the finite-TM2 model.

The preliminary normalization for this reverse construction is now proved.
`TM2Alphabet` supplies a finite set containing all reachable tagged symbols,
without assuming finite internal alphabet types. `TM2Micro` replaces each
macro-step by individual operations, proves refinement of `TM2.stepAux` and
bounded actual runs, and gives a fixed multiplicative overhead. Halting is
absorbing, so the exact time horizon can be any larger polynomial bound.
`TM2MicroSupport` proves finite control/symbol support and the stack-length
bound at every intermediate step. Each microstep makes at most one push;
created persistent nodes can therefore use the microstep time alone as their
unique key. Positive-rule simulation, input interpretation, tuple coding,
and the reverse theorem itself remain to be implemented.

The persistent-node semantics and its positive closure are now proved in
`PersistentStack`, `NodeMachine`, `TimedNodes`, `NodeInput`, `NodeTrace`,
`NodeClosure`, and `NodeAcceptance`. The initial list has an explicit node
representation, time names make each push fresh, and the positive least
fixed point contains exactly the actual bounded computation. Its acceptance
predicate agrees with the output of the original TM2. The remaining reverse
obligation is the concrete FO(LFP) presentation: interpret initial input
nodes, encode finite controls/symbols and bounded node/time addresses, compile
the explicit transition cases to positive rules, separate pointed parameters,
and patch small domains. See the latest `CURRENT_STATE.md` section; no
expressibility or rule-to-machine correspondence is assumed.

The concrete input-position and symbol interpretation is now proved in
`InputSegments`, `InputSegmentFormulas`, `InputTupleCodes`,
`InputPositionFormulas`, and `InputBitFormulas`. It preserves the exact
approved word, supplies injective segment/local-coordinate identifiers, and
defines their padded tuple codes and bit labels by actual first-order syntax.
The remaining initial-node obligation is first/last/successor on this finite
position set and its correspondence with the adjacent entries used by
`NodeInput.records`. Use restricted lexicographic order on the coded positions
so that empty segments and padding gaps are skipped. This link interpretation
must be proved before the initial positive node rules can be instantiated.

That link obligation is now proved in `InputOrder`, `SortedLinks`, and
`InputLinkFormulas`. `OrderedRecords` and `RenameRecords` identify the
order-defined graph with the actual immutable initial records; `InitialInput`
connects it to the alphabet-converted bundled machine input and its represented
run. `SimulationHorizon` supplies a coarse tuple-clock horizon and correct
positive-closure acceptance for every actual polynomial-time witness.
The main remaining construction is the finite FO(LFP) rule presentation of
the supported machine transitions, with fixed-arity node/configuration codes,
parameter separation, and integration of the proved small-domain patch.

Fixed-arity coding and direct free-query parameterization are now proved in
`NodeSupport`, `TupleCoding`, `SupportedCodes`, `NodeCodes`, `FactSupport`,
`FactCodes`, `TraceCodes`, and `ParameterizedRules`. Use this parameterized
compiler; the older all-query-prefix plan above is superseded. The codes are
injective on the supported bounded trace, never on all unbounded raw facts.
`RuleConstants` binds the finite numeral block by actual first-order guards.

The first concrete transition family is complete: `ControlRules` and
`PlainControl` enumerate the stack-preserving cases, and `PlainClosure`
proves both encoded-trace preservation and derivation of every corresponding
bounded step. Reuse `FactPatterns` for the remaining tuple patterns and
`ControlValues` for decoding configuration premises. Every rule has a clock
successor guard; the fresh push node uses the source clock.

Next implement push, pop/peek, and initialization rules, with matching
preservation/derivation lemmas. Push needs separate configuration and record
heads. Nonempty pop/peek has a positive node premise and finite supported
typed symbol cases; the empty case explicitly matches the empty-head code.
Initial node rules use the already proved input bit and next/last formulas.
Then assemble their finite list, identify its LFP with `TraceCodes.encoded`,
read the accepting output, and integrate finite small-domain exceptions.
Only after that may the final reverse assumption be removed and the
authorized submission completed.

All transition families are now concrete and proved. `TransitionRules.rules`
combines plain transitions, the two push conclusions, and empty/nonempty
pop/peek. Its operator preserves the actual encoded trace.
`TransitionDerivation.step` and `added` derive every bounded semantic step
and emitted record. `TransitionClosure.encoded_subset` proves that any
relation containing the initial configuration/records and closed under the
concrete transition rules contains the whole encoded canonical trace.

The next obligation is the concrete initialization compiler, not another
transition simulation. Use one first-clock/first-input-position configuration
rule and four bit/parent-shape node rules. Prove their operator yields exactly
the encoded initial facts, then combine them with the transition list and
discharge `TransitionClosure`'s seed hypotheses for the actual least fixed
point. Those hypotheses must not become final theorem assumptions. Acceptance
extraction and the existing small-domain patch then complete the reverse
direction, subject to full validation and the authorized submission.
