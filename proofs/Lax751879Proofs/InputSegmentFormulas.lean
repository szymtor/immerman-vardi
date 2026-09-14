import Lax751879Proofs.InputSegments
import Lax751879Proofs.AddressFormulas

namespace Lax751879Proofs.InputSegmentFormulas

open Lax751879.OrderedStructures Lax751879.FixedPointSyntax
open Lax751879.FixedPointSemantics
open InputSegments FormulaMacros

/-- Query coordinates and local addresses are ordinary element variables. -/
def valid {σ : Vocabulary} {m v : Nat} {ρ : List Nat}
    (query : Fin m → Fin v) : (s : Segment σ m) →
      (Fin s.arity → Fin v) → RawFormula σ v ρ
  | .coordinate i, x => .less (x 0) (query i)
  | _, _ => .truth

def symbol {σ : Vocabulary} {m v : Nat} {ρ : List Nat} :
    (s : Segment σ m) → (Fin s.arity → Fin v) → RawFormula σ v ρ
  | .header, _ | .coordinate _, _ => .truth
  | .headerEnd, _ | .coordinateEnd _, _ => .neg .truth
  | .table r, x => .relation r x

theorem valid_firstOrder {σ : Vocabulary} {m v : Nat} {ρ : List Nat}
    (query : Fin m → Fin v) (s : Segment σ m) (x : Fin s.arity → Fin v) :
    FirstOrder (valid (ρ := ρ) query s x) := by cases s <;> trivial

theorem symbol_firstOrder {σ : Vocabulary} {m v : Nat} {ρ : List Nat}
    (s : Segment σ m) (x : Fin s.arity → Fin v) :
    FirstOrder (symbol (ρ := ρ) s x) := by cases s <;> trivial

theorem eval_valid {σ : Vocabulary} {m v : Nat} {ρ : List Nat}
    (query : Fin m → Fin v) (s : Segment σ m) (x : Fin s.arity → Fin v)
    (A : OrderedStructure σ) (a : Fin v → Fin A.size) (η : RelationEnv A.size ρ) :
    eval (valid query s x) A a η ↔ a ∘ x ∈ locals ⟨A, a ∘ query⟩ s := by
  rw [mem_locals]
  cases s <;> rfl

theorem eval_symbol {σ : Vocabulary} {m v : Nat} {ρ : List Nat}
    (s : Segment σ m) (x : Fin s.arity → Fin v)
    (A : OrderedStructure σ) (a : Fin v → Fin A.size) (query : Fin m → Fin A.size)
    (η : RelationEnv A.size ρ) :
    eval (symbol s x) A a η ↔ bit ⟨A, query⟩ s (a ∘ x) = true := by
  cases s <;> simp [symbol, bit, eval]

end Lax751879Proofs.InputSegmentFormulas
