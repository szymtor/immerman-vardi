import Lax979537Proofs.InputPositionFormulas

namespace Lax979537Proofs.InputBitFormulas

open Lax979537.OrderedStructures Lax979537.FixedPointSyntax
open Lax979537.FixedPointSemantics
open InputSegments InputSegmentFormulas InputTupleCodes InputPositionFormulas
open FormulaMacros TupleOrder

def hasBit {σ : Vocabulary} {m v w : Nat} {ρ : List Nat}
    (hw : ∀ s : Segment σ m, s.arity ≤ w) (query : Fin m → Fin v)
    (addr : Fin (w + 1) → Fin v) (b : Bool) : RawFormula σ v ρ :=
  anyOf ((segments σ m).map fun s =>
    .conj (presentation hw query s (addr 0) (fun i => addr i.succ))
      (let φ := symbol s (fun i => addr (Fin.castLE (hw s) i).succ)
       if b then φ else .neg φ))

theorem hasBit_firstOrder {σ : Vocabulary} {m v w : Nat} {ρ : List Nat}
    (hw : ∀ s : Segment σ m, s.arity ≤ w) (query : Fin m → Fin v)
    (addr : Fin (w + 1) → Fin v) (b : Bool) :
    FirstOrder (hasBit (ρ := ρ) hw query addr b) := by
  rw [hasBit, firstOrder_anyOf]
  intro _ h
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp h
  refine ⟨presentation_firstOrder _ _ _ _ _, ?_⟩
  cases b <;> exact symbol_firstOrder _ _

theorem eval_symbol_coded {σ : Vocabulary} {m v w : Nat} {ρ : List Nat}
    (hw : ∀ s : Segment σ m, s.arity ≤ w) (s : Segment σ m)
    (addr : Fin (w + 1) → Fin v) (A : OrderedStructure σ)
    (hn : tagBound σ m ≤ A.size) (a : Fin v → Fin A.size)
    (query : Fin m → Fin A.size) (η : RelationEnv A.size ρ)
    (x : Fin s.arity → Fin A.size) (hc : code hn hw ⟨s, x⟩ = a ∘ addr) :
    eval (symbol s (fun i => addr (Fin.castLE (hw s) i).succ)) A a η ↔
      bit ⟨A, query⟩ s x = true := by
  rw [eval_symbol _ _ A a query η]
  have he := ((code_eq_iff hn hw s x (a ∘ addr)).mp hc).2.1
  change (a ∘ (fun i => addr (Fin.castLE (hw s) i).succ)) = x at he
  rw [he]

/-- The actual first-order formula recognizes exactly the labeled positions
of the approved input word. No arithmetic offset relation is assumed. -/
theorem eval_hasBit {σ : Vocabulary} {m v w : Nat} {ρ : List Nat}
    (hw : ∀ s : Segment σ m, s.arity ≤ w) (query : Fin m → Fin v)
    (addr : Fin (w + 1) → Fin v) (b : Bool) (A : OrderedStructure σ)
    (hn : tagBound σ m ≤ A.size) (a : Fin v → Fin A.size) (η : RelationEnv A.size ρ) :
    eval (hasBit hw query addr b) A a η ↔
      ∃ p ∈ positions ⟨A, a ∘ query⟩,
        code hn hw p = a ∘ addr ∧ bit ⟨A, a ∘ query⟩ p.1 p.2 = b := by
  have he : Fin.cons (a (addr 0)) (a ∘ (fun i => addr i.succ)) = a ∘ addr := by
    funext i; exact Fin.cases rfl (fun _ => rfl) i
  simp only [hasBit, eval_anyOf, exists_map, mem_segments, true_and, eval]
  constructor
  · rintro ⟨s, hp, hb⟩
    obtain ⟨x, hx, hc⟩ := (eval_presentation_coded hw query s _ _ A hn a η).mp hp
    rw [he] at hc
    refine ⟨⟨s, x⟩, (mem_positions _ _).mpr hx, hc, ?_⟩
    have hs := eval_symbol_coded hw s addr A hn a (a ∘ query) η x hc
    cases b <;> simpa only [Bool.false_eq_true, ↓reduceIte, eval, hs, Bool.not_eq_true] using hb
  · rintro ⟨⟨s, x⟩, hx, hc, hb⟩
    refine ⟨s, (eval_presentation_coded hw query s _ _ A hn a η).mpr
      ⟨x, (mem_positions _ _).mp hx, he.symm ▸ hc⟩, ?_⟩
    have hs := eval_symbol_coded hw s addr A hn a (a ∘ query) η x hc
    cases b <;> simpa only [Bool.false_eq_true, ↓reduceIte, eval, hs, Bool.not_eq_true] using hb

end Lax979537Proofs.InputBitFormulas
