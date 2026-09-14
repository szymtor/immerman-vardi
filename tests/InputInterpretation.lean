import Lax751879Proofs.InputBitFormulas
import Lax751879Proofs.InputLinkFormulas
import Lax751879Proofs.InitialInput
import Lax751879Proofs.SimulationHorizon

open Lax751879.OrderedStructures Lax751879.StructureEncoding
open Lax751879Proofs
open InputSegments InputTupleCodes InputPositionFormulas InputBitFormulas

namespace InputInterpretationTest

def exampleInput : PointedStructure [0, 1] 2 :=
  ⟨⟨8, fun r => by
    refine Fin.cases (fun _ => true) ?_ r
    intro j
    change Fin 1 at j
    have : j = 0 := Subsingleton.elim _ _
    subst j
    change (Fin 1 → Fin 8) → Bool
    exact fun x => decide ((x 0).val % 2 = 0)⟩, ![0, 7]⟩

/-- Includes a nullary relation, an alternating unary table, an empty unary
query segment, and a maximal query coordinate. -/
example : word exampleInput =
    List.replicate 8 true ++ [false, true] ++
      [true, false, true, false, true, false, true, false] ++
      [false] ++ List.replicate 7 true ++ [false] := by decide

example : (positions exampleInput).length = 27 := by decide

example : locals exampleInput (.coordinate 0) = [] := by decide

def emptyInput : PointedStructure [0, 1] 0 :=
  ⟨⟨0, fun r => by
    refine Fin.cases (fun _ => true) ?_ r
    intro j
    change Fin 1 at j
    have : j = 0 := Subsingleton.elim _ _
    subst j
    change (Fin 1 → Fin 0) → Bool
    exact fun x => Fin.elim0 (x 0)⟩, Fin.elim0⟩

/-- Empty universes retain the header delimiter and the nullary table bit. -/
example : word emptyInput = [false, true] := by decide

example : (positions emptyInput).Nodup := positions_nodup _

example (i : Fin (encode exampleInput).length) :
    bit exampleInput (ids exampleInput i).1 (ids exampleInput i).2 =
      (encode exampleInput).get i := ids_bit _ _

example : Function.Injective
    (code (σ := [0, 1]) (m := 2) (n := 8) (by decide) arity_le_width) :=
  code_injective _ _

def testRank : Identifier [0, 1] 2 8 → Nat :=
  InputOrder.rank exampleInput (by decide) arity_le_width

def positionAt (i : Fin 27) : Identifier [0, 1] 2 8 :=
  (positions exampleInput).get (Fin.cast (by decide) i)

/-- The empty first coordinate block is skipped between a relation table
and that coordinate's delimiter. -/
example : (positionAt 17).1 = .table 1 := by decide
example : (positionAt 18).1 = .coordinateEnd 0 := by decide
example : (positionAt 19).1 = .coordinate 1 := by decide

example : SortedLinks.Next (positions exampleInput) testRank (positionAt 17) (positionAt 18) :=
  (SortedLinks.next_get _ _ (InputOrder.rank_sorted exampleInput (by decide) arity_le_width) _ _).mpr rfl

example : ¬SortedLinks.Next (positions exampleInput) testRank (positionAt 17) (positionAt 19) := by
  unfold testRank positionAt
  rw [SortedLinks.next_get _ _ (InputOrder.rank_sorted exampleInput (by decide) arity_le_width)]
  decide

example : SortedLinks.First (positions exampleInput) testRank (positionAt 0) :=
  (SortedLinks.first_get _ _ (InputOrder.rank_sorted exampleInput (by decide) arity_le_width) _).mpr rfl

example : SortedLinks.Last (positions exampleInput) testRank (positionAt 26) :=
  (SortedLinks.last_get _ _ (InputOrder.rank_sorted exampleInput (by decide) arity_le_width) _).mpr rfl

/-- The actual formula matches adjacent indices, for arbitrary parameters
and variable placements, not only these concrete example structures. -/
example {σ : Vocabulary} {m v : Nat} (query : Fin m → Fin v)
    (x y : Fin (width σ + 1) → Fin v) (A : OrderedStructure σ)
    (hn : tagBound σ m ≤ A.size) (a : Fin v → Fin A.size)
    (i j : Fin (positions (⟨A, a ∘ query⟩ : PointedStructure σ m)).length)
    (hx : code hn arity_le_width ((positions ⟨A, a ∘ query⟩).get i) = a ∘ x)
    (hy : code hn arity_le_width ((positions ⟨A, a ∘ query⟩).get j) = a ∘ y) :
    Lax751879.FixedPointSemantics.eval (InputLinkFormulas.next (ρ := []) arity_le_width query x y)
      A a (fun i => Fin.elim0 i) ↔ i.val + 1 = j.val :=
  (InputLinkFormulas.eval_next_coded _ _ _ _ _ _ _ _ _ _ hx hy).trans
    (SortedLinks.next_get _ _ (InputOrder.rank_sorted _ hn arity_le_width) i j)

/-- The formula bridge is uniform over vocabulary, query arity, relation
contents, and every sufficiently large finite ordered universe. -/
example {σ : Vocabulary} {m v : Nat} (query : Fin m → Fin v)
    (addr : Fin (width σ + 1) → Fin v) (b : Bool) (A : OrderedStructure σ)
    (hn : tagBound σ m ≤ A.size) (a : Fin v → Fin A.size) :
    Lax751879.FixedPointSemantics.eval (hasBit (ρ := []) arity_le_width query addr b) A a
      (fun i => Fin.elim0 i) ↔
    ∃ p ∈ positions ⟨A, a ∘ query⟩,
      code hn arity_le_width p = a ∘ addr ∧ bit ⟨A, a ∘ query⟩ p.1 p.2 = b :=
  eval_hasBit _ _ _ _ _ _ _ _

#print axioms InputSegments.word_eq_encode
#print axioms InputSegments.ids_injective
#print axioms InputSegments.ids_bit
#print axioms InputTupleCodes.code_injective
#print axioms InputPositionFormulas.eval_position
#print axioms InputBitFormulas.eval_hasBit
#print axioms InputOrder.positions_sorted
#print axioms InputLinkFormulas.eval_next
#print axioms OrderedRecords.records_iff
#print axioms InitialInput.heap_iff
#print axioms InitialInput.head_iff
#print axioms InitialInput.represented_run
#print axioms SimulationHorizon.exists_horizon
#print axioms SimulationHorizon.exists_deciding_horizon

end InputInterpretationTest
