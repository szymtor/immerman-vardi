import Lax979537Proofs.InputTupleCodes

namespace Lax979537Proofs.InputPositionFormulas

open Lax979537.OrderedStructures Lax979537.FixedPointSyntax
open Lax979537.FixedPointSemantics
open InputSegments InputSegmentFormulas InputTupleCodes FormulaMacros TupleOrder

theorem code_eq_iff {σ : Vocabulary} {m n w : Nat} (hn : tagBound σ m ≤ n)
    (hw : ∀ s : Segment σ m, s.arity ≤ w) (s : Segment σ m)
    (x : Fin s.arity → Fin n) (b : Fin (w + 1) → Fin n) :
    code hn hw ⟨s, x⟩ = b ↔
      (b 0).val = tag s ∧ (fun i => b (Fin.castLE (hw s) i).succ) = x ∧
      ∀ i : Fin w, s.arity ≤ i.val → (b i.succ).val = 0 := by
  constructor
  · intro h
    refine ⟨congrArg Fin.val (congrFun h 0).symm, ?_, ?_⟩
    · funext i
      simpa only [code_local] using (congrFun h (Fin.castLE (hw s) i).succ).symm
    · intro i hi
      have he := congrArg (fun z : Fin n => z.val) (congrFun h i.succ).symm
      simpa [code, Nat.not_lt.mpr hi] using he
  · rintro ⟨ht, hx, hp⟩
    funext i
    refine Fin.cases ?_ ?_ i
    · exact Fin.ext ht.symm
    · intro j
      by_cases hj : j.val < s.arity
      · have he := congrFun hx ⟨j.val, hj⟩
        simpa [code, hj] using he.symm
      · apply Fin.ext
        simpa [code, hj] using (hp j (Nat.le_of_not_lt hj)).symm

theorem eval_presentation_coded {σ : Vocabulary} {m v w : Nat} {ρ : List Nat}
    (hw : ∀ s : Segment σ m, s.arity ≤ w) (query : Fin m → Fin v)
    (s : Segment σ m) (tagVar : Fin v) (dataVars : Fin w → Fin v)
    (A : OrderedStructure σ) (hn : tagBound σ m ≤ A.size)
    (a : Fin v → Fin A.size) (η : RelationEnv A.size ρ) :
    eval (presentation hw query s tagVar dataVars) A a η ↔
      ∃ x ∈ locals ⟨A, a ∘ query⟩ s,
        code hn hw ⟨s, x⟩ = Fin.cons (a tagVar) (a ∘ dataVars) := by
  rw [eval_presentation]
  simp only [code_eq_iff, Fin.cons_zero, Fin.cons_succ]
  constructor
  · rintro ⟨ht, hx, hp⟩
    exact ⟨a ∘ (dataVars ∘ Fin.castLE (hw s)), hx, ht, rfl, hp⟩
  · rintro ⟨x, hx, ht, he, hp⟩
    refine ⟨ht, ?_, hp⟩
    simpa only [← he, Function.comp_def] using hx

def position {σ : Vocabulary} {m v w : Nat} {ρ : List Nat}
    (hw : ∀ s : Segment σ m, s.arity ≤ w) (query : Fin m → Fin v)
    (addr : Fin (w + 1) → Fin v) : RawFormula σ v ρ :=
  anyOf ((segments σ m).map fun s =>
    presentation hw query s (addr 0) (fun i => addr i.succ))

theorem position_firstOrder {σ : Vocabulary} {m v w : Nat} {ρ : List Nat}
    (hw : ∀ s : Segment σ m, s.arity ≤ w) (query : Fin m → Fin v)
    (addr : Fin (w + 1) → Fin v) : FirstOrder (position (ρ := ρ) hw query addr) := by
  rw [position, firstOrder_anyOf]
  exact fun _ h => by
    obtain ⟨s, _, rfl⟩ := List.mem_map.mp h
    exact presentation_firstOrder _ _ _ _ _

theorem eval_position {σ : Vocabulary} {m v w : Nat} {ρ : List Nat}
    (hw : ∀ s : Segment σ m, s.arity ≤ w) (query : Fin m → Fin v)
    (addr : Fin (w + 1) → Fin v) (A : OrderedStructure σ)
    (hn : tagBound σ m ≤ A.size) (a : Fin v → Fin A.size) (η : RelationEnv A.size ρ) :
    eval (position hw query addr) A a η ↔
      ∃ p ∈ positions ⟨A, a ∘ query⟩, code hn hw p = a ∘ addr := by
  simp only [position, eval_anyOf, exists_map, eval_presentation_coded hw query _ _ _ A hn,
    mem_segments, true_and]
  have he : Fin.cons (a (addr 0)) (a ∘ (fun i => addr i.succ)) = a ∘ addr := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  rw [he]
  constructor
  · rintro ⟨s, x, hx, hc⟩
    exact ⟨⟨s, x⟩, (mem_positions _ _).mpr hx, hc⟩
  · rintro ⟨⟨s, x⟩, hx, hc⟩
    exact ⟨s, x, (mem_positions _ _).mp hx, hc⟩

end Lax979537Proofs.InputPositionFormulas
