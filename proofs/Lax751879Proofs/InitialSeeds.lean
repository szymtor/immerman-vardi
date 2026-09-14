import Lax751879Proofs.InitialConfigSemantics
import Lax751879Proofs.InitialNodes

namespace Lax751879Proofs.InitialSeeds

open Turing Lax751879.OrderedStructures

noncomputable def rules (tm : FinTM2) (e : tm.Γ tm.k₀ ≃ Bool) (σ : Vocabulary) (m d w : Nat) :
    List (ParameterizedRules.Rule σ m (FactCodes.payloadWidth tm d w + 1)) :=
  RuleConstants.compile (InitialConfigRules.rule tm σ m d w) :: InitialNodes.rules tm e σ m d w

theorem operator_iff (tm : FinTM2) (e : tm.Γ tm.k₀ ≃ Bool) {σ : Vocabulary} {m : Nat}
    (d : Nat) (A : PointedStructure σ m) (hn : TraceCodes.threshold tm σ m ≤ A.structureValue.size)
    (R : Set (Fin (TraceCodes.arity tm σ d) → Fin A.structureValue.size))
    (out : Fin (TraceCodes.arity tm σ d) → Fin A.structureValue.size) :
    out ∈ ParameterizedRules.operator (rules tm e σ m d (TraceCodes.nodeWidth σ d)) A.structureValue A.tuple R ↔
      TraceCodes.code tm d A hn (.config 0 (NodeInput.config tm (InitialInput.raw tm e A) (InitialInput.names tm e A))) = out ∨
      ∃ r ∈ NodeInput.heap tm (InitialInput.raw tm e A) (InitialInput.names tm e A), TraceCodes.code tm d A hn (.node r) = out := by
  constructor
  · rintro ⟨r, hr, ho⟩
    rcases List.mem_cons.mp hr with rfl | hr
    · exact Or.inl ((InitialConfigSemantics.holds tm e d A hn R out).mp ho)
    · exact Or.inr ((InitialNodes.operator_iff tm e d A hn R out).mp ⟨r, hr, ho⟩)
  · rintro (hc | hr)
    · exact ⟨_, List.mem_cons_self .., (InitialConfigSemantics.holds tm e d A hn R out).mpr hc⟩
    · obtain ⟨r, hr, ho⟩ := (InitialNodes.operator_iff tm e d A hn R out).mpr hr
      exact ⟨r, List.mem_cons_of_mem _ hr, ho⟩

theorem preserves {f : List Bool → Bool} (h : TM2ComputableInPolyTime id (fun b : Bool => [b]) f)
    {σ : Vocabulary} {m : Nat} (d : Nat) (A : PointedStructure σ m)
    (hn : TraceCodes.threshold h.tm σ m ≤ A.structureValue.size)
    (R : Set (Fin (TraceCodes.arity h.tm σ d) → Fin A.structureValue.size)) :
    ParameterizedRules.operator (rules h.tm h.inputAlphabet σ m d (TraceCodes.nodeWidth σ d))
      A.structureValue A.tuple R ⊆ TraceCodes.encoded h d A hn := by
  intro out ho
  rcases (operator_iff h.tm h.inputAlphabet d A hn R out).mp ho with hc | ⟨r, hr, he⟩
  · refine ⟨.config 0 (SimulationHorizon.context h A).config, ?_, hc⟩
    rw [← NodeClosure.closure_fixed]
    exact Or.inl ⟨rfl, rfl⟩
  · refine ⟨.node r, ?_, he⟩
    rw [← NodeClosure.closure_fixed]
    exact Or.inl hr

end Lax751879Proofs.InitialSeeds
