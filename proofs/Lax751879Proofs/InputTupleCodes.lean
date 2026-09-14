import Lax751879Proofs.InputSegmentFormulas
import Mathlib.Algebra.Order.BigOperators.Group.List

namespace Lax751879Proofs.InputTupleCodes

open Lax751879.OrderedStructures Lax751879.FixedPointSyntax
open Lax751879.FixedPointSemantics
open InputSegments InputSegmentFormulas FormulaMacros TupleOrder AddressFormulas

def tag {σ : Vocabulary} {m : Nat} : Segment σ m → Nat
  | .header => 0
  | .headerEnd => 1
  | .table r => 2 + r.val
  | .coordinate i => 2 + σ.length + 2 * i.val
  | .coordinateEnd i => 3 + σ.length + 2 * i.val

def tagBound (σ : Vocabulary) (m : Nat) : Nat := 2 + σ.length + 2 * m

theorem tag_lt {σ : Vocabulary} {m : Nat} (s : Segment σ m) :
    tag s < tagBound σ m := by cases s <;> simp only [tag, tagBound] <;> omega

theorem tag_injective {σ : Vocabulary} {m : Nat} :
    Function.Injective (tag (σ := σ) (m := m)) := by
  intro s t h
  cases s <;> cases t <;> simp only [tag] at h
  all_goals first | rfl | (congr 1; apply Fin.ext; omega) | omega

/-- A fixed-width tuple: one segment tag, followed by local coordinates and
zero padding. The width bound is independent of the input structure. -/
def code {σ : Vocabulary} {m n w : Nat} (hn : tagBound σ m ≤ n)
    (_hw : ∀ s : Segment σ m, s.arity ≤ w) (p : Identifier σ m n) :
    Fin (w + 1) → Fin n :=
  Fin.cons ⟨tag p.1, Nat.lt_of_lt_of_le (tag_lt p.1) hn⟩
    (fun i => if h : i.val < p.1.arity then p.2 ⟨i.val, h⟩
      else ⟨0, by have := tag_lt (Segment.header (σ := σ) (m := m)); simp only [tag] at this; omega⟩)

theorem code_zero {σ : Vocabulary} {m n w : Nat} (hn : tagBound σ m ≤ n)
    (hw : ∀ s : Segment σ m, s.arity ≤ w) (p : Identifier σ m n) :
    (code hn hw p 0).val = tag p.1 := rfl

theorem code_local {σ : Vocabulary} {m n w : Nat} (hn : tagBound σ m ≤ n)
    (hw : ∀ s : Segment σ m, s.arity ≤ w) (p : Identifier σ m n)
    (i : Fin p.1.arity) : code hn hw p (Fin.castLE (hw p.1) i).succ = p.2 i := by
  simp [code, i.isLt]

theorem code_injective {σ : Vocabulary} {m n w : Nat} (hn : tagBound σ m ≤ n)
    (hw : ∀ s : Segment σ m, s.arity ≤ w) : Function.Injective (code hn hw) := by
  rintro ⟨s, x⟩ ⟨t, y⟩ h
  have ht : s = t := tag_injective (congrArg Fin.val (congrFun h 0))
  subst t
  congr 1
  funext i
  have hi := congrFun h (Fin.castLE (hw s) i).succ
  simpa only [code_local] using hi

def presentation {σ : Vocabulary} {m v w : Nat} {ρ : List Nat}
    (hw : ∀ s : Segment σ m, s.arity ≤ w) (query : Fin m → Fin v)
    (s : Segment σ m) (tagVar : Fin v) (dataVars : Fin w → Fin v) : RawFormula σ v ρ :=
  .conj (numeral (tag s) tagVar)
    (.conj (valid query s (dataVars ∘ Fin.castLE (hw s)))
      (allOf ((List.finRange w).map fun i =>
        if i.val < s.arity then .truth else numeral 0 (dataVars i))))

theorem presentation_firstOrder {σ : Vocabulary} {m v w : Nat} {ρ : List Nat}
    (hw : ∀ s : Segment σ m, s.arity ≤ w) (query : Fin m → Fin v)
    (s : Segment σ m) (tagVar : Fin v) (dataVars : Fin w → Fin v) :
    FirstOrder (presentation (ρ := ρ) hw query s tagVar dataVars) := by
  refine ⟨numeral_firstOrder _ _, valid_firstOrder _ _ _, ?_⟩
  simp only [firstOrder_allOf, List.forall_mem_map, List.mem_finRange, forall_const]
  intro i
  split <;> trivial

theorem eval_presentation {σ : Vocabulary} {m v w : Nat} {ρ : List Nat}
    (hw : ∀ s : Segment σ m, s.arity ≤ w) (query : Fin m → Fin v)
    (s : Segment σ m) (tagVar : Fin v) (dataVars : Fin w → Fin v)
    (A : OrderedStructure σ) (a : Fin v → Fin A.size) (η : RelationEnv A.size ρ) :
    eval (presentation hw query s tagVar dataVars) A a η ↔
      (a tagVar).val = tag s ∧
      a ∘ (dataVars ∘ Fin.castLE (hw s)) ∈ locals ⟨A, a ∘ query⟩ s ∧
      ∀ i : Fin w, s.arity ≤ i.val → (a (dataVars i)).val = 0 := by
  simp only [presentation, eval, eval_numeral, eval_valid, eval_allOf,
    List.forall_mem_map, List.mem_finRange, forall_const]
  apply and_congr_right; intro _
  apply and_congr_right; intro _
  apply forall_congr'
  intro i
  split <;> simp_all [eval, eval_numeral]

def width (σ : Vocabulary) : Nat := σ.sum + 1

theorem arity_le_width {σ : Vocabulary} {m : Nat} (s : Segment σ m) :
    s.arity ≤ width σ := by
  cases s with
  | header | headerEnd | coordinate | coordinateEnd => simp [width, Segment.arity]
  | table r =>
      exact (List.le_sum_of_mem (List.get_mem σ r)).trans (Nat.le_succ _)

end Lax751879Proofs.InputTupleCodes
