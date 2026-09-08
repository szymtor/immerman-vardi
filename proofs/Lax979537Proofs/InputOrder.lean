import Lax979537Proofs.InputTupleCodes

namespace Lax979537Proofs.InputOrder

open Lax979537.OrderedStructures Lax979537.StructureEncoding
open InputSegments InputTupleCodes TupleOrder TupleAddresses

theorem finRange_sorted (n : Nat) : (List.finRange n).Pairwise (· < ·) := by
  rw [List.pairwise_iff_get]
  intro i j hij
  simpa using hij

theorem tuples_sorted (n k : Nat) : (tuples n k).Pairwise TupleLex := by
  induction k with
  | zero => simp [tuples]
  | succ k ih =>
      rw [tuples, List.pairwise_flatMap]
      refine ⟨fun a _ => List.pairwise_map.mpr (ih.imp ?_), (finRange_sorted n).imp ?_⟩
      · intro x y h
        exact (lex_succ _ _).mpr (Or.inr ⟨rfl, by simpa using h⟩)
      · intro a b hab x hx y hy
        obtain ⟨u, _, rfl⟩ := List.mem_map.mp hx
        obtain ⟨v, _, rfl⟩ := List.mem_map.mp hy
        exact (lex_succ _ _).mpr (Or.inl hab)

theorem locals_sorted {σ : Vocabulary} {m : Nat} (A : PointedStructure σ m)
    (s : Segment σ m) : (locals A s).Pairwise TupleLex := by
  cases s with
  | header =>
      apply List.pairwise_map.mpr
      exact (finRange_sorted _).imp (fun {_ _} h => ⟨0, h, fun i hi => (Fin.not_lt_zero i hi).elim⟩)
  | headerEnd | coordinateEnd => simp [locals]
  | table r => exact tuples_sorted _ _
  | coordinate j =>
      apply List.pairwise_map.mpr
      exact (finRange_sorted _).imp (fun {_ _} h => ⟨0, h, fun i hi => (Fin.not_lt_zero i hi).elim⟩)

theorem segments_sorted (σ : Vocabulary) (m : Nat) :
    (segments σ m).Pairwise (fun s t => tag s < tag t) := by
  have ht : ((List.finRange σ.length).map (Segment.table (m := m))).Pairwise
      (fun s t => tag s < tag t) := by
    apply List.pairwise_map.mpr
    exact (finRange_sorted _).imp (fun {_ _} h => by simpa only [tag, Nat.add_lt_add_iff_left] using h)
  have hc : ((List.finRange m).flatMap
      (fun i => [Segment.coordinate (σ := σ) i, .coordinateEnd i])).Pairwise
      (fun s t => tag s < tag t) := by
    apply List.pairwise_flatMap.mpr
    refine ⟨fun i _ => by simp [tag], (finRange_sorted _).imp ?_⟩
    intro i j hij x hx y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp only [tag] <;> omega
  apply List.pairwise_append.mpr
  refine ⟨?_, hc, ?_⟩
  · apply List.pairwise_append.mpr
    refine ⟨by simp [tag], ht, ?_⟩
    intro x hx y hy
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> simp only [tag] <;> omega
  · intro x hx y hy
    obtain ⟨i, _, hy⟩ := List.mem_flatMap.mp hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases List.mem_append.mp hx with hx | hx
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp [tag] <;> omega
    · obtain ⟨r, _, rfl⟩ := List.mem_map.mp hx
      rcases hy with rfl | rfl <;> simp only [tag] <;> omega

theorem code_lex_of_tag {σ : Vocabulary} {m n w : Nat} (hn : tagBound σ m ≤ n)
    (hw : ∀ s : Segment σ m, s.arity ≤ w) (p q : Identifier σ m n)
    (h : tag p.1 < tag q.1) : TupleLex (code hn hw p) (code hn hw q) :=
  ⟨0, h, fun i hi => (Fin.not_lt_zero i hi).elim⟩

theorem code_lex_of_local {σ : Vocabulary} {m n w : Nat} (hn : tagBound σ m ≤ n)
    (hw : ∀ s : Segment σ m, s.arity ≤ w) (s : Segment σ m)
    (x y : Fin s.arity → Fin n) (h : TupleLex x y) :
    TupleLex (code hn hw ⟨s, x⟩) (code hn hw ⟨s, y⟩) := by
  obtain ⟨i, hi, hp⟩ := h
  refine ⟨(Fin.castLE (hw s) i).succ, by simpa only [code_local] using hi, ?_⟩
  intro j hj
  refine Fin.cases ?_ ?_ j hj
  · intro _; rfl
  · intro k hk
    have hki : k.val < i.val := by simpa using hk
    have hks : k.val < s.arity := hki.trans i.isLt
    simpa [code, hks] using hp ⟨k.val, hks⟩ hki

/-- Valid input positions occur in strictly increasing order of their padded
tuple codes, so restricted tuple successor recovers the original word order. -/
theorem positions_sorted {σ : Vocabulary} {m w : Nat} (A : PointedStructure σ m)
    (hn : tagBound σ m ≤ A.structureValue.size)
    (hw : ∀ s : Segment σ m, s.arity ≤ w) :
    (positions A).Pairwise (fun p q => TupleLex (code hn hw p) (code hn hw q)) := by
  apply List.pairwise_flatMap.mpr
  refine ⟨fun s _ => ?_, (segments_sorted σ m).imp ?_⟩
  · apply List.pairwise_map.mpr
    exact (locals_sorted A s).imp (fun {_ _} h => code_lex_of_local hn hw s _ _ h)
  · intro s t h p hp q hq
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hp
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hq
    exact code_lex_of_tag hn hw _ _ h

def rank {σ : Vocabulary} {m w : Nat} (A : PointedStructure σ m)
    (hn : tagBound σ m ≤ A.structureValue.size)
    (hw : ∀ s : Segment σ m, s.arity ≤ w) (p : Identifier σ m A.structureValue.size) : Nat :=
  (address A.structureValue.size (w + 1) (code hn hw p)).val

theorem rank_sorted {σ : Vocabulary} {m w : Nat} (A : PointedStructure σ m)
    (hn : tagBound σ m ≤ A.structureValue.size)
    (hw : ∀ s : Segment σ m, s.arity ≤ w) :
    (positions A).Pairwise (fun p q => rank A hn hw p < rank A hn hw q) :=
  (positions_sorted A hn hw).imp (fun {_ _} h => (address_lt_iff _ _ _ _).mpr h)

end Lax979537Proofs.InputOrder
