import Lax979537Proofs.DecoderSoundness
import Lax979537Proofs.NodeInput
import Mathlib.Data.List.Nodup

namespace Lax979537Proofs.InputSegments

open Lax979537.OrderedStructures Lax979537.StructureEncoding

/-- Fixed input segments, independent of the size and contents of a structure. -/
inductive Segment (σ : Vocabulary) (m : Nat) where
  | header
  | headerEnd
  | table (r : Fin σ.length)
  | coordinate (i : Fin m)
  | coordinateEnd (i : Fin m)
  deriving DecidableEq

def segments (σ : Vocabulary) (m : Nat) : List (Segment σ m) :=
  [.header, .headerEnd] ++ (List.finRange σ.length).map .table ++
    (List.finRange m).flatMap (fun i => [.coordinate i, .coordinateEnd i])

@[reducible] def Segment.arity {σ : Vocabulary} {m : Nat} : Segment σ m → Nat
  | .header | .coordinate _ => 1
  | .headerEnd | .coordinateEnd _ => 0
  | .table r => σ.get r

abbrev Identifier (σ : Vocabulary) (m n : Nat) :=
  (s : Segment σ m) × (Fin s.arity → Fin n)

def locals {σ : Vocabulary} {m : Nat} (A : PointedStructure σ m) :
    (s : Segment σ m) → List (Fin s.arity → Fin A.structureValue.size)
  | .header => (List.finRange A.structureValue.size).map (fun a _ => a)
  | .headerEnd => [Fin.elim0]
  | .table r => tuples A.structureValue.size (σ.get r)
  | .coordinate i => (List.finRange (A.tuple i).val).map
      (fun a _ => ⟨a.val, Nat.lt_trans a.isLt (A.tuple i).isLt⟩)
  | .coordinateEnd _ => [Fin.elim0]

def bit {σ : Vocabulary} {m : Nat} (A : PointedStructure σ m) :
    (s : Segment σ m) → (Fin s.arity → Fin A.structureValue.size) → Bool
  | .header, _ | .coordinate _, _ => true
  | .headerEnd, _ | .coordinateEnd _, _ => false
  | .table r, x => A.structureValue.relation r x

def positions {σ : Vocabulary} {m : Nat} (A : PointedStructure σ m) :
    List (Identifier σ m A.structureValue.size) :=
  (segments σ m).sigma (locals A)

theorem mem_segments {σ : Vocabulary} {m : Nat} (s : Segment σ m) :
    s ∈ segments σ m := by cases s <;> simp [segments]

theorem mem_positions {σ : Vocabulary} {m : Nat} (A : PointedStructure σ m)
    (p : Identifier σ m A.structureValue.size) :
    p ∈ positions A ↔ p.2 ∈ locals A p.1 := by
  rcases p with ⟨s, x⟩
  simp only [positions, List.mem_sigma, mem_segments, true_and]

def word {σ : Vocabulary} {m : Nat} (A : PointedStructure σ m) : List Bool :=
  (positions A).map (fun p => bit A p.1 p.2)

theorem segments_nodup (σ : Vocabulary) (m : Nat) : (segments σ m).Nodup := by
  have ht : ((List.finRange σ.length).map (Segment.table (m := m))).Nodup :=
    (List.nodup_finRange _).map (fun _ _ h => Segment.table.inj h)
  have hc : ((List.finRange m).flatMap
      (fun i => [Segment.coordinate (σ := σ) i, .coordinateEnd i])).Nodup := by
    apply List.nodup_flatMap.mpr
    refine ⟨fun i _ => by simp, (List.nodup_finRange m).imp ?_⟩
    intro i j hij x hx hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
    rcases hx with rfl | rfl <;> simp_all
  apply List.nodup_append'.mpr
  refine ⟨?_, hc, ?_⟩
  · apply List.nodup_append'.mpr
    refine ⟨by simp, ht, ?_⟩
    intro x hx hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases List.mem_map.mp hy with ⟨r, _, rfl⟩
    rcases hx with h | h <;> cases h
  · intro x hx hy
    rcases List.mem_flatMap.mp hy with ⟨i, _, hi⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> simp at hx

theorem locals_nodup {σ : Vocabulary} {m : Nat} (A : PointedStructure σ m)
    (s : Segment σ m) : (locals A s).Nodup := by
  cases s with
  | header =>
      exact (List.nodup_finRange _).map (fun _ _ h => congrFun h 0)
  | headerEnd | coordinateEnd => simp [locals]
  | table r => exact DecoderSoundness.tuples_nodup _ _
  | coordinate i =>
      apply (List.nodup_finRange _).map
      intro a b h
      exact Fin.ext (congrArg (fun z : Fin A.structureValue.size => z.val) (congrFun h 0))

theorem positions_nodup {σ : Vocabulary} {m : Nat} (A : PointedStructure σ m) :
    (positions A).Nodup := (segments_nodup σ m).sigma (locals_nodup A)

theorem word_eq_encode {σ : Vocabulary} {m : Nat} (A : PointedStructure σ m) :
    word A = encode A := by
  simp [word, positions, List.sigma, segments, locals, bit, encode, unary,
    List.map_flatMap, List.flatMap_map, List.flatMap_assoc, List.map_map,
    Function.comp_def, List.map_const', List.append_assoc]

/-- A segment's local coordinates are valid precisely when they occur in
the canonical input enumeration. Only query-coordinate segments are restricted. -/
theorem mem_locals {σ : Vocabulary} {m : Nat} (A : PointedStructure σ m)
    (s : Segment σ m) (x : Fin s.arity → Fin A.structureValue.size) :
    x ∈ locals A s ↔ match s with
      | .coordinate i => (x 0).val < (A.tuple i).val
      | _ => True := by
  cases s with
  | header =>
      simp only [locals, List.mem_map, List.mem_finRange, true_and, iff_true]
      exact ⟨x 0, by funext i; have : i = 0 := Subsingleton.elim _ _; subst i; rfl⟩
  | headerEnd | coordinateEnd => simp [locals, Subsingleton.elim x Fin.elim0]
  | table r => exact iff_true_intro (StructureEncoding.mem_tuples _ _ _)
  | coordinate i =>
      simp only [locals, List.mem_map, List.mem_finRange, true_and]
      constructor
      · rintro ⟨a, rfl⟩; exact a.isLt
      · intro h
        refine ⟨⟨(x 0).val, h⟩, ?_⟩
        funext j
        have : j = 0 := Subsingleton.elim _ _
        subst j
        rfl

theorem positions_length {σ : Vocabulary} {m : Nat} (A : PointedStructure σ m) :
    (positions A).length = (encode A).length := by
  simpa only [word, List.length_map] using congrArg List.length (word_eq_encode A)

/-- The concrete initial identifiers required by the persistent-node simulation. -/
def ids {σ : Vocabulary} {m : Nat} (A : PointedStructure σ m)
    (i : Fin (encode A).length) : Identifier σ m A.structureValue.size :=
  (positions A).get (Fin.cast (positions_length A).symm i)

theorem ids_injective {σ : Vocabulary} {m : Nat} (A : PointedStructure σ m) :
    Function.Injective (ids A) := by
  intro i j h
  have he := (positions_nodup A).injective_get h
  exact Fin.ext (congrArg (fun k : Fin (positions A).length => k.val) he)

theorem ids_bit {σ : Vocabulary} {m : Nat} (A : PointedStructure σ m)
    (i : Fin (encode A).length) :
    bit A (ids A i).1 (ids A i).2 = (encode A).get i := by
  have h := congrArg (fun xs : List Bool => xs[i.val]?) (word_eq_encode A)
  have hi : i.val < (positions A).length := by rw [positions_length]; exact i.isLt
  simpa [word, ids, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem i.isLt] using h

end Lax979537Proofs.InputSegments
