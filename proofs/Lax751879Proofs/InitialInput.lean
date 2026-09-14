import Lax751879Proofs.InputOrder
import Lax751879Proofs.OrderedRecords
import Lax751879Proofs.RenameRecords

namespace Lax751879Proofs.InitialInput

open Turing Lax751879.OrderedStructures Lax751879.StructureEncoding
open InputSegments InputTupleCodes InputOrder

def listIds {α β : Type} (xs : List α) (f : α → β) (i : Fin (xs.map f).length) : α :=
  xs.get (Fin.cast (List.length_map (f := f)) i)

theorem listIds_injective {α β : Type} (xs : List α) (f : α → β) (h : xs.Nodup) :
    Function.Injective (listIds xs f) := by
  intro i j he
  have hi := h.injective_get he
  exact Fin.ext (congrArg (fun k : Fin xs.length => k.val) hi)

theorem entries_map (tm : FinTM2) {α : Type} (xs : List α) (f : α → tm.Γ tm.k₀) :
    NodeInput.entries tm (xs.map f) (listIds xs f) =
      xs.map (fun p => (Sum.inl p, Sigma.mk tm.k₀ (f p))) := by
  apply List.ext_getElem
  · simp [NodeInput.entries]
  · intro i hi hj
    simp [NodeInput.entries, listIds, List.get_eq_getElem]

variable (tm : FinTM2) (e : tm.Γ tm.k₀ ≃ Bool) {σ : Vocabulary} {m : Nat}
  (A : PointedStructure σ m)

def raw : List (tm.Γ tm.k₀) :=
  (positions A).map (fun p => e.symm (bit A p.1 p.2))

def names : Fin (raw tm e A).length → Identifier σ m A.structureValue.size :=
  listIds (positions A) (fun p => e.symm (bit A p.1 p.2))

theorem raw_eq_encode : raw tm e A = (encode A).map e.symm := by
  rw [← word_eq_encode]
  simp only [raw, word, List.map_map]
  rfl

theorem names_injective : Function.Injective (names tm e A) :=
  listIds_injective _ _ (positions_nodup A)

theorem entries_eq : NodeInput.entries tm (raw tm e A) (names tm e A) =
    (positions A).map (fun p => (Sum.inl p, Sigma.mk tm.k₀ (e.symm (bit A p.1 p.2)))) :=
  entries_map tm _ _

theorem head_iff {w : Nat} (hn : tagBound σ m ≤ A.structureValue.size)
    (hw : ∀ s : Segment σ m, s.arity ≤ w)
    (p : Identifier σ m A.structureValue.size) :
    NodeInput.head (NodeInput.entries tm (raw tm e A) (names tm e A)) = some (Sum.inl p) ↔
      SortedLinks.First (positions A) (rank A hn hw) p := by
  rw [entries_eq, ← OrderedRecords.head_iff (positions A) (rank A hn hw)
    (rank_sorted A hn hw) (fun _ => ()) p, OrderedRecords.head_map]
  simp only [NodeInput.head, List.head?_map, Option.map_map, Function.comp_def]
  constructor
  · exact fun h => Option.map_injective Sum.inl_injective h
  · exact fun h => congrArg (Option.map Sum.inl) h

/-- The concrete segment graph is exactly the initial persistent-node heap
for the bundled machine's alphabet-converted approved input. -/
theorem heap_iff {w : Nat} (hn : tagBound σ m ≤ A.structureValue.size)
    (hw : ∀ s : Segment σ m, s.arity ≤ w)
    (n : TimedNodes.Node (Identifier σ m A.structureValue.size))
    (a : Sigma tm.Γ) (parent : Option (TimedNodes.Node (Identifier σ m A.structureValue.size))) :
    (n, a, parent) ∈ NodeInput.heap tm (raw tm e A) (names tm e A) ↔
      ∃ p parent₀, Sum.inl p = n ∧ parent₀.map Sum.inl = parent ∧
        p ∈ positions A ∧ a = Sigma.mk tm.k₀ (e.symm (bit A p.1 p.2)) ∧
        OrderedRecords.Parent (positions A) (rank A hn hw) p parent₀ := by
  rw [NodeInput.heap, entries_eq]
  have he : (positions A).map (fun p =>
      (Sum.inl p, Sigma.mk tm.k₀ (e.symm (bit A p.1 p.2)))) =
      RenameRecords.entries (Sum.inl : Identifier σ m A.structureValue.size → TimedNodes.Node _)
        ((positions A).map (fun p => (p, Sigma.mk tm.k₀ (e.symm (bit A p.1 p.2))))) := by
    simp [RenameRecords.entries, List.map_map]
  rw [he, RenameRecords.records_entries]
  simp_rw [OrderedRecords.records_iff (positions A) (rank A hn hw) (rank_sorted A hn hw)]

theorem represented_run (t : Nat) :
    ∃ H c, TimedNodes.Run tm.m (NodeInput.heap tm (raw tm e A) (names tm e A))
      (NodeInput.config tm (raw tm e A) (names tm e A)) t H c ∧
      PersistentStack.Functional H ∧ TimedNodes.Bounded H t ∧
      NodeMachine.Matches H c ((TM2Micro.next tm.m)^[t]
        (TM2Micro.boundary (initList tm ((encode A).map e.symm)))) := by
  simpa only [← raw_eq_encode tm e A] using
    NodeInput.represented_run tm (raw tm e A) (names tm e A) (names_injective tm e A) t

end Lax751879Proofs.InitialInput
