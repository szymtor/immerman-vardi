import Lax751879Proofs.AddressFormulas
import Lax751879Proofs.StructureEncoding
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Prod

namespace Lax751879Proofs.FiniteExceptions

open Lax751879.OrderedStructures Lax751879.FixedPointSyntax
open Lax751879.FixedPointSemantics Lax751879.StructureEncoding
open TupleOrder FormulaMacros AddressFormulas

def relationDiagram {σ : Vocabulary} {m n : Nat} (r : Symbol σ)
    (a : Fin (σ.get r) → Fin n) (b : Bool) : RawFormula σ m [] :=
  existsBlock (σ.get r)
    (.conj
      (allOf ((List.finRange (σ.get r)).map fun i =>
        numeral (a i).val (Fin.castAdd m i)))
      (if b then .relation r (Fin.castAdd m) else .neg (.relation r (Fin.castAdd m))))

theorem relationDiagram_firstOrder {σ : Vocabulary} {m n : Nat}
    (r : Symbol σ) (a : Fin (σ.get r) → Fin n) (b : Bool) :
    FirstOrder (relationDiagram (m := m) r a b) := by
  apply (firstOrder_existsBlock _ _).mpr
  constructor
  · simp only [firstOrder_allOf, List.forall_mem_map]
    exact fun i _ => numeral_firstOrder _ _
  · cases b <;> trivial

theorem eval_relationDiagram {σ : Vocabulary} {m n : Nat}
    (r : Symbol σ) (a : Fin (σ.get r) → Fin n) (b : Bool)
    (S : (r : Symbol σ) → (Fin (σ.get r) → Fin n) → Bool)
    (v : Fin m → Fin n) :
    eval (relationDiagram r a b) ⟨n, S⟩ v (fun i => Fin.elim0 i) ↔ S r a = b := by
  cases b <;>
    simp only [relationDiagram, Bool.false_eq_true, ↓reduceIte, eval_existsBlock,
      eval, eval_allOf, List.forall_mem_map, List.mem_finRange, forall_const,
      eval_numeral, Fin.append_left]
  all_goals
    have hh : ∀ w : Fin (σ.get r) → Fin n,
        (∀ i, (w i).val = (a i).val) ↔ w = a := by
      intro w
      simp only [← Fin.ext_iff, funext_iff]
    have ha : ∀ w : Fin (σ.get r) → Fin n,
        Fin.append w v ∘ Fin.castAdd m = w := by intro w; funext i; simp
    simp only [hh, ha]
    simp

def diagramRaw {σ : Vocabulary} {k : Nat} (A : PointedStructure σ k) :
    RawFormula σ k [] :=
  .conj (sizeExactly A.structureValue.size)
    (.conj
      (allOf ((List.finRange k).map fun i => numeral (A.tuple i).val i))
      (allOf ((List.finRange σ.length).flatMap fun r =>
        (tuples A.structureValue.size (σ.get r)).map fun a =>
          relationDiagram r a (A.structureValue.relation r a))))

theorem diagramRaw_firstOrder {σ : Vocabulary} {k : Nat} (A : PointedStructure σ k) :
    FirstOrder (diagramRaw A) := by
  refine ⟨sizeExactly_firstOrder _, ?_, ?_⟩
  · simp only [firstOrder_allOf, List.forall_mem_map]
    exact fun i _ => numeral_firstOrder _ _
  · simp only [firstOrder_allOf, List.forall_mem_flatMap, List.forall_mem_map]
    exact fun r _ a _ => relationDiagram_firstOrder r a _

theorem eval_diagram_same_size {σ : Vocabulary} {k n : Nat}
    (R S : (r : Symbol σ) → (Fin (σ.get r) → Fin n) → Bool)
    (a b : Fin k → Fin n) :
    eval (diagramRaw ⟨⟨n, R⟩, a⟩) ⟨n, S⟩ b (fun i => Fin.elim0 i) ↔
      b = a ∧ S = R := by
  simp only [diagramRaw, eval, eval_sizeExactly, true_and, eval_allOf,
    List.forall_mem_map, List.forall_mem_flatMap, List.mem_finRange, forall_const,
    eval_numeral, eval_relationDiagram, StructureEncoding.mem_tuples]
  constructor
  · rintro ⟨hb, hS⟩
    exact ⟨funext (fun i => Fin.ext (hb i)), funext (fun r => funext (hS r))⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨fun _ => rfl, fun _ _ => rfl⟩

theorem eval_diagramRaw {σ : Vocabulary} {k : Nat} (A B : PointedStructure σ k) :
    eval (diagramRaw A) B.structureValue B.tuple (fun i => Fin.elim0 i) ↔ B = A := by
  rcases A with ⟨⟨n, R⟩, a⟩
  rcases B with ⟨⟨s, S⟩, b⟩
  constructor
  · intro h
    have hs : s = n := (eval_sizeExactly n ⟨s, S⟩ b _).mp h.1
    subst s
    obtain ⟨rfl, rfl⟩ := (eval_diagram_same_size R S a b).mp h
    rfl
  · intro h
    cases h
    exact (eval_diagram_same_size R R a a).mpr ⟨rfl, rfl⟩

/-- A finite first-order diagram of a canonical ordered pointed structure.
This includes nullary relation bits even when the domain is empty. -/
def diagram {σ : Vocabulary} {k : Nat} (A : PointedStructure σ k) : Formula σ k :=
  ⟨diagramRaw A, firstOrder_admissible _ (diagramRaw_firstOrder A)⟩

abbrev AtSize (σ : Vocabulary) (k n : Nat) :=
  ((r : Symbol σ) → (Fin (σ.get r) → Fin n) → Bool) × (Fin k → Fin n)

def toPointed {σ : Vocabulary} {k N : Nat}
    (c : (n : Fin (N + 1)) × AtSize σ k n.val) : PointedStructure σ k :=
  ⟨⟨c.1.val, c.2.1⟩, c.2.2⟩

noncomputable def candidates (σ : Vocabulary) (k N : Nat) :
    List (PointedStructure σ k) := by
  classical
  exact (Finset.univ : Finset ((n : Fin (N + 1)) × AtSize σ k n.val)).toList.map toPointed

theorem mem_candidates {σ : Vocabulary} {k N : Nat} (A : PointedStructure σ k) :
    A ∈ candidates σ k N ↔ A.structureValue.size ≤ N := by
  classical
  simp only [candidates, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨c, rfl⟩
    exact Nat.le_of_lt_succ c.1.isLt
  · intro h
    exact ⟨⟨⟨A.structureValue.size, Nat.lt_succ_of_le h⟩,
      A.structureValue.relation, A.tuple⟩, rfl⟩

/-- Any query restricted to a fixed finite domain-size bound has a finite
first-order definition. This discharges the exceptional small domains in the
tuple-based machine simulation, for arbitrary vocabulary and query arity. -/
noncomputable def boundedFormula {σ : Vocabulary} {k : Nat}
    (Q : Query σ k) (N : Nat) : Formula σ k := by
  classical
  refine ⟨anyOf (((candidates σ k N).filter fun A => decide (Q A)).map diagramRaw), ?_⟩
  rw [admissible_anyOf]
  simp only [List.forall_mem_map]
  exact fun A _ => firstOrder_admissible _ (diagramRaw_firstOrder A)

theorem satisfies_boundedFormula {σ : Vocabulary} {k : Nat}
    (Q : Query σ k) (N : Nat) (A : PointedStructure σ k) :
    Satisfies A (boundedFormula Q N) ↔ A.structureValue.size ≤ N ∧ Q A := by
  classical
  simp only [Satisfies, boundedFormula, eval_anyOf, exists_map, List.mem_filter,
    mem_candidates, decide_eq_true_eq, eval_diagramRaw]
  constructor
  · rintro ⟨B, hB, rfl⟩
    exact hB
  · intro hA
    exact ⟨A, hA, rfl⟩

theorem bounded_definable {σ : Vocabulary} {k : Nat} (Q : Query σ k) (N : Nat) :
    Definable (fun A => A.structureValue.size ≤ N ∧ Q A) :=
  ⟨boundedFormula Q N, fun A => (satisfies_boundedFormula Q N A).symm⟩

/-- Complete a definition valid on sufficiently large domains by adding the
finite diagram disjunction for the exceptional domains. -/
noncomputable def patchSmall {σ : Vocabulary} {k : Nat}
    (Q : Query σ k) (N : Nat) (φ : Formula σ k) : Formula σ k :=
  ⟨disj (boundedFormula Q N).val (.conj (.neg (sizeAtMost N)) φ.val),
    ⟨(boundedFormula Q N).property,
      (firstOrder_admissible (sizeAtMost N) (numeral_firstOrder N 0)), φ.property⟩⟩

theorem definable_of_above {σ : Vocabulary} {k : Nat} (Q : Query σ k)
    (N : Nat) (φ : Formula σ k)
    (hφ : ∀ A, N < A.structureValue.size → (Q A ↔ Satisfies A φ)) : Definable Q := by
  refine ⟨patchSmall Q N φ, fun A => ?_⟩
  change Q A ↔ eval (patchSmall Q N φ).val A.structureValue A.tuple _
  rw [patchSmall, eval_disj]
  change Q A ↔ Satisfies A (boundedFormula Q N) ∨
    (¬eval (sizeAtMost N) A.structureValue A.tuple _) ∧ Satisfies A φ
  rw [satisfies_boundedFormula, eval_sizeAtMost]
  by_cases h : A.structureValue.size ≤ N
  · simp [h]
  · simp only [h, false_and, false_or, not_false_eq_true, true_and]
    exact hφ A (by omega)

end Lax751879Proofs.FiniteExceptions
