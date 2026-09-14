import Lax751879Proofs.TransitionDerivation

namespace Lax751879Proofs.TransitionClosure

open Turing Lax751879.OrderedStructures NodeClosure NodeTrace

variable {f : List Bool → Bool} (h : TM2ComputableInPolyTime id (fun b : Bool => [b]) f)
    {σ : Vocabulary} {m : Nat} (d : Nat) (A : PointedStructure σ m)
    (hn : TraceCodes.threshold h.tm σ m ≤ A.structureValue.size)

/-- Once the initial configuration and records are present, closure under
the concrete transition rules derives each canonical snapshot and its heap. -/
theorem at_time
    (R : Set (Fin (TraceCodes.arity h.tm σ d) → Fin A.structureValue.size))
    (hclosed : ParameterizedRules.operator (TransitionRules.rules h.tm σ m d (TraceCodes.nodeWidth σ d))
      A.structureValue A.tuple R ⊆ R)
    (hinit : TraceCodes.code h.tm d A hn (.config 0 (SimulationHorizon.context h A).config) ∈ R)
    (hnodes : ∀ r ∈ (SimulationHorizon.context h A).heap, TraceCodes.code h.tm d A hn (.node r) ∈ R)
    (t : Nat) (ht : t < A.structureValue.size ^ d) :
    TraceCodes.code h.tm d A hn (.config t (snapshot (SimulationHorizon.context h A) t).2) ∈ R ∧
      ∀ r ∈ (snapshot (SimulationHorizon.context h A) t).1, TraceCodes.code h.tm d A hn (.node r) ∈ R := by
  induction t with
  | zero =>
      rw [snapshot_zero]
      exact ⟨hinit, hnodes⟩
  | succ t ih =>
      obtain ⟨hcfg, hheap⟩ := ih (by omega)
      have hsem := trace_in_closure (SimulationHorizon.context h A) (A.structureValue.size ^ d - 1) t (by omega)
      have hvalid := TraceCodes.closure_valid h d A hn _ hsem.1
      have hsupport : ∀ r ∈ (snapshot (SimulationHorizon.context h A) t).1, r.2.1 ∈ TM2Alphabet.alphabet h.tm :=
        fun r hr => (TraceCodes.closure_valid h d A hn (.node r) (hsem.2 hr)).2.1
      have hs := snapshot_step (SimulationHorizon.context h A) t
      constructor
      · exact hclosed (TransitionDerivation.step h d A hn hs hvalid.2.1 ht R hcfg hsupport hheap)
      · intro r hr
        rcases (NodeMachine.step_records hs r).mp hr with hold | hnew
        · exact hheap r hold
        · exact hclosed (TransitionDerivation.added h d A hn
            (snapshot (SimulationHorizon.context h A) t).2 r hnew hvalid.2.1 ht R hcfg)

/-- A closure principle for the concrete rules. The remaining initialization
compiler must prove the two seed hypotheses for its actual LFP. -/
theorem encoded_subset
    (R : Set (Fin (TraceCodes.arity h.tm σ d) → Fin A.structureValue.size))
    (hclosed : ParameterizedRules.operator (TransitionRules.rules h.tm σ m d (TraceCodes.nodeWidth σ d))
      A.structureValue A.tuple R ⊆ R)
    (hinit : TraceCodes.code h.tm d A hn (.config 0 (SimulationHorizon.context h A).config) ∈ R)
    (hnodes : ∀ r ∈ (SimulationHorizon.context h A).heap, TraceCodes.code h.tm d A hn (.node r) ∈ R) :
    TraceCodes.encoded h d A hn ⊆ R := by
  have hnpos : 0 < A.structureValue.size := by unfold TraceCodes.threshold at hn; omega
  have hpow : 0 < A.structureValue.size ^ d := Nat.pow_pos hnpos
  rintro out ⟨fact, hf, rfl⟩
  rw [closure_eq_trace] at hf
  cases fact with
  | config t cfg =>
      rcases hf with ⟨ht, rfl⟩
      exact (at_time h d A hn R hclosed hinit hnodes t (by omega)).1
  | node r =>
      exact (at_time h d A hn R hclosed hinit hnodes (A.structureValue.size ^ d - 1) (by omega)).2 r hf

end Lax751879Proofs.TransitionClosure
