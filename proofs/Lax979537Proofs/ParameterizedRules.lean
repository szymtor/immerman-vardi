import Lax979537Proofs.PositiveRules

namespace Lax979537Proofs.ParameterizedRules

open Lax979537.OrderedStructures Lax979537.FixedPointSyntax
open Lax979537.FixedPointSemantics Lax979537.LeastFixedPoints
open SyntaxOperations TupleOrder FormulaMacros

/-- A positive rule with designated free query parameters. Parameters stay
outside the fixed-point relation and are shared by every rule application. -/
structure Rule (σ : Vocabulary) (m k : Nat) extends PositiveRules.Rule σ k where
  parameters : Fin m → Fin numVars

def Rule.holds {σ : Vocabulary} {m k : Nat} (r : Rule σ m k)
    (A : OrderedStructure σ) (q : Fin m → Fin A.size)
    (R : Set (Fin k → Fin A.size)) (a : Fin k → Fin A.size) : Prop :=
  ∃ v : Fin r.numVars → Fin A.size,
    eval r.guard A v (fun i => Fin.elim0 i) ∧ v ∘ r.parameters = q ∧
      v ∘ r.head = a ∧ ∀ b ∈ r.premises, v ∘ b ∈ R

def Rule.matrix {σ : Vocabulary} {m k : Nat} (r : Rule σ m k) :
    RawFormula σ (r.numVars + (k + m)) [k] :=
  .conj (rename (copyFO r.guard [k]) (Fin.castAdd (k + m)))
    (.conj (allOf ((List.finRange m).map fun i =>
      .equal (Fin.castAdd (k + m) (r.parameters i)) (Fin.natAdd r.numVars (Fin.natAdd k i))))
      (.conj (allOf ((List.finRange k).map fun i =>
        .equal (Fin.castAdd (k + m) (r.head i)) (Fin.natAdd r.numVars (Fin.castAdd m i))))
        (allOf (r.premises.map fun b => .variable 0 (Fin.castAdd (k + m) ∘ b)))))

def Rule.formula {σ : Vocabulary} {m k : Nat} (r : Rule σ m k) : RawFormula σ (k + m) [k] :=
  existsBlock r.numVars r.matrix

theorem Rule.formula_admissible {σ : Vocabulary} {m k : Nat} (r : Rule σ m k) :
    r.formula.Admissible := by
  apply (existsBlock_admissible _ _).mpr
  refine ⟨(rename_admissible _ _).mpr (copyFO_admissible _ _), ?_, ?_, ?_⟩
  all_goals simp [admissible_allOf, RawFormula.Admissible]

theorem Rule.formula_positive {σ : Vocabulary} {m k : Nat} (r : Rule σ m k) :
    r.formula.positiveAt 0 true := by
  apply (existsBlock_positive _ _ _ _).mpr
  refine ⟨(rename_positiveAt _ _ _ _).mpr (copyFO_positive _ _ _ _), ?_, ?_, ?_⟩
  all_goals simp [positive_allOf, RawFormula.positiveAt]

theorem Rule.eval_formula {σ : Vocabulary} {m k : Nat} (r : Rule σ m k)
    (A : OrderedStructure σ) (q : Fin m → Fin A.size) (a : Fin k → Fin A.size)
    (η : RelationEnv A.size [k]) :
    eval r.formula A (Fin.append a q) η ↔ r.holds A q (η 0) a := by
  rw [Rule.formula, eval_existsBlock]
  apply exists_congr
  intro v
  simp only [Rule.matrix, eval, eval_rename, eval_allOf, List.forall_mem_map,
    List.mem_finRange, forall_const, Fin.append_left, Fin.append_right]
  have hv : Fin.append v (Fin.append a q) ∘ Fin.castAdd (k + m) = v := by
    funext i; simp
  rw [hv, eval_copyFO _ r.guard_firstOrder _ A v (fun i => Fin.elim0 i)]
  simp only [← Function.comp_assoc, hv]
  change (_ ∧ (∀ i, v (r.parameters i) = q i) ∧ (∀ i, v (r.head i) = a i) ∧ _) ↔
    (_ ∧ v ∘ r.parameters = q ∧ v ∘ r.head = a ∧ _)
  exact and_congr_right (fun _ => and_congr funext_iff.symm
    (and_congr funext_iff.symm Iff.rfl))

def operator {σ : Vocabulary} {m k : Nat} (rs : List (Rule σ m k))
    (A : OrderedStructure σ) (q : Fin m → Fin A.size) (R : Set (Fin k → Fin A.size)) :
    Set (Fin k → Fin A.size) := {a | ∃ r ∈ rs, r.holds A q R a}

theorem operator_monotone {σ : Vocabulary} {m k : Nat} (rs : List (Rule σ m k))
    (A : OrderedStructure σ) (q : Fin m → Fin A.size) : Monotone (operator rs A q) := by
  intro R S h a
  rintro ⟨r, hr, v, hg, hq, ha, hp⟩
  exact ⟨r, hr, v, hg, hq, ha, fun b hb => h (hp b hb)⟩

def body {σ : Vocabulary} {m k : Nat} (rs : List (Rule σ m k)) : RawFormula σ (k + m) [k] :=
  anyOf (rs.map Rule.formula)

def bodyFor {σ : Vocabulary} {m k v : Nat} (rs : List (Rule σ m k))
    (query : Fin m → Fin v) : RawFormula σ (k + v) [k] :=
  rename (body rs) (Fin.addCases (Fin.castAdd v) (Fin.natAdd k ∘ query))

def membership {σ : Vocabulary} {m k v : Nat} (rs : List (Rule σ m k))
    (query : Fin m → Fin v) (args : Fin k → Fin v) : RawFormula σ v [] :=
  .lfp k (bodyFor rs query) args

theorem membership_admissible {σ : Vocabulary} {m k v : Nat} (rs : List (Rule σ m k))
    (query : Fin m → Fin v) (args : Fin k → Fin v) : (membership rs query args).Admissible := by
  constructor
  · apply (rename_admissible _ _).mpr
    simp only [body, admissible_anyOf, List.forall_mem_map]
    exact fun r _ => r.formula_admissible
  · apply (rename_positiveAt _ _ _ _).mpr
    simp only [body, positive_anyOf, List.forall_mem_map]
    exact fun r _ => r.formula_positive

theorem bodyOperator_eq {σ : Vocabulary} {m k v : Nat} (rs : List (Rule σ m k))
    (query : Fin m → Fin v) (A : OrderedStructure σ) (a : Fin v → Fin A.size) :
    bodyOperator (bodyFor rs query) A a (fun i => Fin.elim0 i) = operator rs A (a ∘ query) := by
  funext R
  ext t
  have he : Fin.append t a ∘ Fin.addCases (Fin.castAdd v) (Fin.natAdd k ∘ query) =
      Fin.append t (a ∘ query) := by
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp
    · intro j; simp
  simp only [bodyOperator, bodyFor, Set.mem_setOf_eq, eval_rename, he, body,
    eval_anyOf, exists_map, Rule.eval_formula, operator]
  rfl

/-- An actual LFP formula defines exactly the finite positive-rule closure
at the current free query valuation. No facts from other valuations enter. -/
theorem eval_membership {σ : Vocabulary} {m k v : Nat} (rs : List (Rule σ m k))
    (query : Fin m → Fin v) (args : Fin k → Fin v)
    (A : OrderedStructure σ) (a : Fin v → Fin A.size) :
    eval (membership rs query args) A a (fun i => Fin.elim0 i) ↔
      a ∘ args ∈ leastFixedPoint (operator rs A (a ∘ query)) := by
  change a ∘ args ∈ leastFixedPoint (bodyOperator (bodyFor rs query) A a _) ↔ _
  rw [bodyOperator_eq]

end Lax979537Proofs.ParameterizedRules
