import Lax751879Proofs.SyntaxOperations

namespace Lax751879Proofs.TupleOrder

open Lax751879.OrderedStructures Lax751879.FixedPointSyntax
open Lax751879.FixedPointSemantics

def disj {σ : Vocabulary} {m : Nat} {ρ : List Nat}
    (φ ψ : RawFormula σ m ρ) : RawFormula σ m ρ :=
  .neg (.conj (.neg φ) (.neg ψ))

def allOf {σ : Vocabulary} {m : Nat} {ρ : List Nat} :
    List (RawFormula σ m ρ) → RawFormula σ m ρ
  | [] => .truth
  | φ :: fs => .conj φ (allOf fs)

def anyOf {σ : Vocabulary} {m : Nat} {ρ : List Nat} :
    List (RawFormula σ m ρ) → RawFormula σ m ρ
  | [] => .neg .truth
  | φ :: fs => disj φ (anyOf fs)

theorem eval_disj {σ : Vocabulary} {m : Nat} {ρ : List Nat}
    (φ ψ : RawFormula σ m ρ) (A : OrderedStructure σ)
    (v : Fin m → Fin A.size) (η : RelationEnv A.size ρ) :
    eval (disj φ ψ) A v η ↔ eval φ A v η ∨ eval ψ A v η := by
  classical
  by_cases h : eval φ A v η <;> simp [disj, eval, h]

theorem eval_allOf {σ : Vocabulary} {m : Nat} {ρ : List Nat}
    (fs : List (RawFormula σ m ρ)) (A : OrderedStructure σ)
    (v : Fin m → Fin A.size) (η : RelationEnv A.size ρ) :
    eval (allOf fs) A v η ↔ ∀ φ ∈ fs, eval φ A v η := by
  induction fs with
  | nil => simp [allOf, eval]
  | cons φ fs ih => simp [allOf, eval, ih]

theorem eval_anyOf {σ : Vocabulary} {m : Nat} {ρ : List Nat}
    (fs : List (RawFormula σ m ρ)) (A : OrderedStructure σ)
    (v : Fin m → Fin A.size) (η : RelationEnv A.size ρ) :
    eval (anyOf fs) A v η ↔ ∃ φ ∈ fs, eval φ A v η := by
  induction fs with
  | nil => simp [anyOf, eval]
  | cons φ fs ih => simp [anyOf, eval_disj, ih]

theorem admissible_allOf {σ : Vocabulary} {m : Nat} {ρ : List Nat}
    (fs : List (RawFormula σ m ρ)) :
    (allOf fs).Admissible ↔ ∀ φ ∈ fs, φ.Admissible := by
  induction fs with
  | nil => simp [allOf, RawFormula.Admissible]
  | cons φ fs ih => simp [allOf, RawFormula.Admissible, ih]

theorem admissible_anyOf {σ : Vocabulary} {m : Nat} {ρ : List Nat}
    (fs : List (RawFormula σ m ρ)) :
    (anyOf fs).Admissible ↔ ∀ φ ∈ fs, φ.Admissible := by
  induction fs with
  | nil => simp [anyOf, RawFormula.Admissible]
  | cons φ fs ih => simp [anyOf, disj, RawFormula.Admissible, ih]

/-- Lexicographic comparison of two tuples of variable indices. This formula
is independent of the size of the input structure. -/
def lexFormula {σ : Vocabulary} {m k : Nat} {ρ : List Nat}
    (x y : Fin k → Fin m) : RawFormula σ m ρ :=
  anyOf ((List.finRange k).map fun i =>
    .conj (.less (x i) (y i))
      (allOf ((List.finRange k).map fun j =>
        if j < i then .equal (x j) (y j) else .truth)))

def TupleLex {n k : Nat} (a b : Fin k → Fin n) : Prop :=
  ∃ i, a i < b i ∧ ∀ j, j < i → a j = b j

theorem exists_map {α β : Type} (xs : List α) (f : α → β) (P : β → Prop) :
    (∃ y ∈ xs.map f, P y) ↔ ∃ x ∈ xs, P (f x) := by
  constructor
  · rintro ⟨y, hy, hp⟩
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    exact ⟨x, hx, hp⟩
  · rintro ⟨x, hx, hp⟩
    exact ⟨f x, List.mem_map.mpr ⟨x, hx, rfl⟩, hp⟩

theorem lexFormula_admissible {σ : Vocabulary} {m k : Nat} {ρ : List Nat}
    (x y : Fin k → Fin m) : (lexFormula (σ := σ) (ρ := ρ) x y).Admissible := by
  simp only [lexFormula, admissible_anyOf, List.forall_mem_map, List.mem_finRange,
    forall_const, RawFormula.Admissible, true_and, admissible_allOf]
  intro i j
  by_cases h : j < i <;> simp [h, RawFormula.Admissible]

theorem eval_lexFormula {σ : Vocabulary} {m k : Nat} {ρ : List Nat}
    (x y : Fin k → Fin m) (A : OrderedStructure σ)
    (v : Fin m → Fin A.size) (η : RelationEnv A.size ρ) :
    eval (lexFormula x y) A v η ↔ TupleLex (v ∘ x) (v ∘ y) := by
  simp only [lexFormula, eval_anyOf, exists_map, List.mem_finRange,
    true_and, eval, eval_allOf, List.forall_mem_map, forall_const, TupleLex,
    Function.comp_apply]
  apply exists_congr
  intro i
  apply and_congr_right
  intro _
  apply forall_congr'
  intro j
  by_cases h : j < i <;> simp [h, eval]

end Lax751879Proofs.TupleOrder
