import Lax979537Proofs.InitialSeeds
import Lax979537Proofs.TransitionClosure

namespace Lax979537Proofs.CompiledRun

open Turing Lax979537.OrderedStructures Lax979537.FixedPointSemantics

/-- A finite positive rule presentation of the initialized machine run. -/
noncomputable def rules (tm : FinTM2) (e : tm.Γ tm.k₀ ≃ Bool) (σ : Vocabulary) (m d : Nat) :
    List (ParameterizedRules.Rule σ m (TraceCodes.arity tm σ d)) :=
  InitialSeeds.rules tm e σ m d (TraceCodes.nodeWidth σ d) ++
    TransitionRules.rules tm σ m d (TraceCodes.nodeWidth σ d)

theorem operator_iff (tm : FinTM2) (e : tm.Γ tm.k₀ ≃ Bool) {σ : Vocabulary} {m d : Nat}
    (A : OrderedStructure σ) (q : Fin m → Fin A.size)
    (R : Set (Fin (TraceCodes.arity tm σ d) → Fin A.size))
    (out : Fin (TraceCodes.arity tm σ d) → Fin A.size) :
    out ∈ ParameterizedRules.operator (rules tm e σ m d) A q R ↔
      out ∈ ParameterizedRules.operator (InitialSeeds.rules tm e σ m d (TraceCodes.nodeWidth σ d)) A q R ∨
      out ∈ ParameterizedRules.operator (TransitionRules.rules tm σ m d (TraceCodes.nodeWidth σ d)) A q R := by
  simp only [ParameterizedRules.operator, rules, Set.mem_setOf_eq, List.mem_append, or_and_right, exists_or]

noncomputable def closure (tm : FinTM2) (e : tm.Γ tm.k₀ ≃ Bool) {σ : Vocabulary} {m : Nat}
    (d : Nat) (A : PointedStructure σ m) : Set (Fin (TraceCodes.arity tm σ d) → Fin A.structureValue.size) :=
  Lax979537.LeastFixedPoints.leastFixedPoint (ParameterizedRules.operator (rules tm e σ m d) A.structureValue A.tuple)

theorem fixed (tm : FinTM2) (e : tm.Γ tm.k₀ ≃ Bool) {σ : Vocabulary} {m : Nat}
    (d : Nat) (A : PointedStructure σ m) :
    ParameterizedRules.operator (rules tm e σ m d) A.structureValue A.tuple (closure tm e d A) = closure tm e d A :=
  LeastFixedPoints.fixedPoint _ (ParameterizedRules.operator_monotone _ _ _)

/-- The actual finite rule LFP is exactly the encoded canonical bounded run.
Initialization and transition correctness are both discharged concretely. -/
theorem closure_eq_encoded {f : List Bool → Bool} (h : TM2ComputableInPolyTime id (fun b : Bool => [b]) f)
    {σ : Vocabulary} {m : Nat} (d : Nat) (A : PointedStructure σ m)
    (hn : TraceCodes.threshold h.tm σ m ≤ A.structureValue.size) :
    closure h.tm h.inputAlphabet d A = TraceCodes.encoded h d A hn := by
  apply Set.Subset.antisymm
  · apply LeastFixedPoints.least
    intro out ho
    rcases (operator_iff h.tm h.inputAlphabet A.structureValue A.tuple _ out).mp ho with hi | ht
    · exact InitialSeeds.preserves h d A hn _ hi
    · exact TransitionRules.preserves h d A hn ht
  · apply TransitionClosure.encoded_subset h d A hn
    · intro out ht
      rw [← fixed]
      exact (operator_iff h.tm h.inputAlphabet A.structureValue A.tuple _ out).mpr (Or.inr ht)
    · rw [← fixed]
      apply (operator_iff h.tm h.inputAlphabet A.structureValue A.tuple _ _).mpr
      exact Or.inl ((InitialSeeds.operator_iff h.tm h.inputAlphabet d A hn _ _).mpr (Or.inl rfl))
    · intro r hr
      rw [← fixed]
      apply (operator_iff h.tm h.inputAlphabet A.structureValue A.tuple _ _).mpr
      exact Or.inl ((InitialSeeds.operator_iff h.tm h.inputAlphabet d A hn _ _).mpr (Or.inr ⟨r, hr, rfl⟩))

theorem eval_membership {f : List Bool → Bool} (h : TM2ComputableInPolyTime id (fun b : Bool => [b]) f)
    {σ : Vocabulary} {m v : Nat} (d : Nat) (A : OrderedStructure σ)
    (hn : TraceCodes.threshold h.tm σ m ≤ A.size)
    (query : Fin m → Fin v) (args : Fin (TraceCodes.arity h.tm σ d) → Fin v) (a : Fin v → Fin A.size) :
    eval (ParameterizedRules.membership (rules h.tm h.inputAlphabet σ m d) query args) A a (fun i => Fin.elim0 i) ↔
      a ∘ args ∈ TraceCodes.encoded h d ⟨A, a ∘ query⟩ hn := by
  rw [ParameterizedRules.eval_membership]
  change a ∘ args ∈ closure h.tm h.inputAlphabet d ⟨A, a ∘ query⟩ ↔ _
  rw [closure_eq_encoded h d ⟨A, a ∘ query⟩ hn]

end Lax979537Proofs.CompiledRun
