import Lax979537Proofs.FormulaMacros
import Lax979537Proofs.LeastFixedPoints

/-!
Compile a finite collection of positive relational inference rules into the
approved FO(LFP) syntax. This is the syntax interface for the finite local
transition table: guards are first-order and every premise refers positively
to the relation being constructed. No logical expressibility is assumed.
-/

namespace Lax979537Proofs.PositiveRules

open Lax979537.OrderedStructures Lax979537.FixedPointSyntax
open Lax979537.FixedPointSemantics Lax979537.LeastFixedPoints
open SyntaxOperations TupleOrder FormulaMacros

structure Rule (σ : Vocabulary) (k : Nat) where
  numVars : Nat
  guard : RawFormula σ numVars []
  guard_firstOrder : FirstOrder guard
  head : Fin k → Fin numVars
  premises : List (Fin k → Fin numVars)

def Rule.holds {σ : Vocabulary} {k : Nat} (r : Rule σ k)
    (A : OrderedStructure σ) (R : Set (Fin k → Fin A.size))
    (a : Fin k → Fin A.size) : Prop :=
  ∃ v : Fin r.numVars → Fin A.size,
    eval r.guard A v (fun i => Fin.elim0 i) ∧ v ∘ r.head = a ∧
      ∀ b ∈ r.premises, v ∘ b ∈ R

def Rule.matrix {σ : Vocabulary} {k : Nat} (r : Rule σ k) :
    RawFormula σ (r.numVars + k) [k] :=
  .conj (rename (copyFO r.guard [k]) (Fin.castAdd k))
    (.conj
      (allOf ((List.finRange k).map fun i =>
        .equal (Fin.castAdd k (r.head i)) (Fin.natAdd r.numVars i)))
      (allOf (r.premises.map fun b => .variable 0 (Fin.castAdd k ∘ b))))

def Rule.formula {σ : Vocabulary} {k : Nat} (r : Rule σ k) :
    RawFormula σ k [k] := existsBlock r.numVars r.matrix

theorem Rule.formula_admissible {σ : Vocabulary} {k : Nat} (r : Rule σ k) :
    r.formula.Admissible := by
  apply (existsBlock_admissible _ _).mpr
  refine ⟨(rename_admissible _ _).mpr (copyFO_admissible _ _), ?_, ?_⟩
  · simp [admissible_allOf, RawFormula.Admissible]
  · simp [admissible_allOf, RawFormula.Admissible]

theorem Rule.formula_positive {σ : Vocabulary} {k : Nat} (r : Rule σ k) :
    r.formula.positiveAt 0 true := by
  apply (existsBlock_positive _ _ _ _).mpr
  refine ⟨(rename_positiveAt _ _ _ _).mpr (copyFO_positive _ _ _ _), ?_, ?_⟩
  · simp [positive_allOf, RawFormula.positiveAt]
  · simp [positive_allOf, RawFormula.positiveAt]

theorem Rule.eval_formula {σ : Vocabulary} {k : Nat} (r : Rule σ k)
    (A : OrderedStructure σ) (a : Fin k → Fin A.size)
    (η : RelationEnv A.size [k]) :
    eval r.formula A a η ↔ r.holds A (η 0) a := by
  rw [Rule.formula, eval_existsBlock]
  apply exists_congr
  intro v
  simp only [Rule.matrix, eval, eval_rename, eval_allOf,
    List.forall_mem_map, List.mem_finRange, forall_const,
    Fin.append_left, Fin.append_right]
  have hv : Fin.append v a ∘ Fin.castAdd k = v := by
    funext i
    simp
  rw [hv, eval_copyFO _ r.guard_firstOrder _ A v (fun i => Fin.elim0 i)]
  simp only [← Function.comp_assoc, hv]
  change (_ ∧ (∀ i, v (r.head i) = a i) ∧ _) ↔
    (_ ∧ v ∘ r.head = a ∧ _)
  exact and_congr_right (fun _ => and_congr (Iff.symm funext_iff) Iff.rfl)

def operator {σ : Vocabulary} {k : Nat} (rs : List (Rule σ k))
    (A : OrderedStructure σ) (R : Set (Fin k → Fin A.size)) :
    Set (Fin k → Fin A.size) := {a | ∃ r ∈ rs, r.holds A R a}

theorem operator_monotone {σ : Vocabulary} {k : Nat}
    (rs : List (Rule σ k)) (A : OrderedStructure σ) : Monotone (operator rs A) := by
  intro R S h a
  rintro ⟨r, hr, v, hv, he, hp⟩
  exact ⟨r, hr, v, hv, he, fun b hb => h (hp b hb)⟩

def body {σ : Vocabulary} {k : Nat} (rs : List (Rule σ k)) :
    RawFormula σ (k + k) [k] :=
  rename (anyOf (rs.map Rule.formula)) (Fin.castAdd k)

def closure {σ : Vocabulary} {k : Nat} (rs : List (Rule σ k)) : Formula σ k :=
  ⟨.lfp k (body rs) id, by
    constructor
    · apply (rename_admissible _ _).mpr
      simp only [admissible_anyOf, List.forall_mem_map]
      exact fun r _ => r.formula_admissible
    · apply (rename_positiveAt _ _ _ _).mpr
      simp only [positive_anyOf, List.forall_mem_map]
      exact fun r _ => r.formula_positive⟩

theorem bodyOperator_eq {σ : Vocabulary} {k : Nat} (rs : List (Rule σ k))
    (A : OrderedStructure σ) (v : Fin k → Fin A.size) :
    bodyOperator (body rs) A v (fun i => Fin.elim0 i) = operator rs A := by
  funext R
  ext a
  simp only [bodyOperator, body, Set.mem_setOf_eq, eval_rename,
    eval_anyOf, exists_map, Rule.eval_formula, operator]
  have ha : Fin.append a v ∘ Fin.castAdd k = a := by funext i; simp
  rw [ha]
  rfl

/-- The generated formula defines exactly the least relation closed under
the supplied finite rules, in the original concept semantics. -/
theorem eval_closure {σ : Vocabulary} {k : Nat} (rs : List (Rule σ k))
    (A : OrderedStructure σ) (v : Fin k → Fin A.size) :
    eval (closure rs).val A v (fun i => Fin.elim0 i) ↔
      v ∈ leastFixedPoint (operator rs A) := by
  change (v ∘ id) ∈ leastFixedPoint (bodyOperator (body rs) A v _) ↔ _
  rw [bodyOperator_eq]
  rfl

end Lax979537Proofs.PositiveRules
