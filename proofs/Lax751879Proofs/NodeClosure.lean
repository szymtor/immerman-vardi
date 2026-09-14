import Lax751879Proofs.NodeTrace
import Lax751879Proofs.LeastFixedPoints

namespace Lax751879Proofs.NodeClosure

open Turing PersistentStack NodeMachine TimedNodes NodeTrace
open Lax751879.LeastFixedPoints

variable {K Λ State Initial : Type} {Γ : K → Type} [DecidableEq K]

inductive Fact (Γ : K → Type) (Λ State Initial : Type)
  | config (time : Nat) (c : NodeMachine.Cfg Γ Λ State (Node Initial))
  | node (r : Node Initial × Sigma Γ × Option (Node Initial))

def nodes (R : Set (Fact Γ Λ State Initial)) : Records (Node Initial) Γ :=
  {r | Fact.node r ∈ R}

/-- Positive computation rules on configuration and immutable-node facts.
The explicit syntax translation to FO(LFP) is a separate obligation. -/
def operator (M : Λ → TM2.Stmt Γ Λ State) (H₀ : Records (Node Initial) Γ)
    (c₀ : NodeMachine.Cfg Γ Λ State (Node Initial)) (T : Nat)
    (R : Set (Fact Γ Λ State Initial)) : Set (Fact Γ Λ State Initial)
  | .node r => r ∈ H₀ ∨ ∃ t c, t < T ∧ Fact.config t c ∈ R ∧ added (.inr t) c = some r
  | .config t c => (t = 0 ∧ c = c₀) ∨ ∃ s d G,
      s < T ∧ t = s + 1 ∧ Fact.config s d ∈ R ∧ Step M (.inr s) (nodes R) d G c

theorem operator_monotone (M : Λ → TM2.Stmt Γ Λ State) (H₀ : Records (Node Initial) Γ)
    (c₀ : NodeMachine.Cfg Γ Λ State (Node Initial)) (T : Nat) : Monotone (operator M H₀ c₀ T) := by
  intro R S h fact hf
  cases fact with
  | node r =>
      rcases hf with hi | ⟨t, c, ht, hc, hr⟩
      · exact Or.inl hi
      · exact Or.inr ⟨t, c, ht, h hc, hr⟩
  | config t c =>
      rcases hf with hi | ⟨s, d, G, hs, ht, hd, hstep⟩
      · exact Or.inl hi
      · obtain ⟨J, hj, _⟩ := step_mono hstep (show nodes R ⊆ nodes S from fun _ hr => h hr)
        exact Or.inr ⟨s, d, J, hs, ht, h hd, hj⟩

def traceFacts (C : Context Γ Λ State Initial) (T : Nat) : Set (Fact Γ Λ State Initial)
  | .node r => r ∈ (snapshot C T).1
  | .config t c => t ≤ T ∧ c = (snapshot C t).2

theorem trace_prefixed (C : Context Γ Λ State Initial) (T : Nat) :
    operator C.program C.heap C.config T (traceFacts C T) ⊆ traceFacts C T := by
  intro fact hf
  cases fact with
  | node r =>
      rcases hf with hi | ⟨t, c, ht, hc, ha⟩
      · have hm := heap_mono C (Nat.zero_le T)
        rw [snapshot_zero] at hm
        exact hm hi
      · rcases hc with ⟨_, rfl⟩
        have hr := (step_records (snapshot_step C t) r).mpr (Or.inr ha)
        exact heap_mono C (by omega : t + 1 ≤ T) hr
  | config t c =>
      rcases hf with ⟨rfl, rfl⟩ | ⟨s, d, G, hs, rfl, hd, hstep⟩
      · exact ⟨Nat.zero_le T, by simp only [snapshot_zero]⟩
      · rcases hd with ⟨_, rfl⟩
        obtain ⟨J, hj, _⟩ := step_mono (snapshot_step C s) (heap_mono C (Nat.le_of_lt hs))
        have he := (step_unique (snapshot_sound C T).1 hstep hj).2
        exact ⟨by omega, he⟩

def closure (C : Context Γ Λ State Initial) (T : Nat) : Set (Fact Γ Λ State Initial) :=
  leastFixedPoint (operator C.program C.heap C.config T)

theorem closure_sound (C : Context Γ Λ State Initial) (T : Nat) : closure C T ⊆ traceFacts C T :=
  LeastFixedPoints.least _ _ (trace_prefixed C T)

theorem closure_fixed (C : Context Γ Λ State Initial) (T : Nat) :
    operator C.program C.heap C.config T (closure C T) = closure C T :=
  LeastFixedPoints.fixedPoint _ (operator_monotone _ _ _ _)

theorem trace_in_closure (C : Context Γ Λ State Initial) (T t : Nat) (ht : t ≤ T) :
    Fact.config t (snapshot C t).2 ∈ closure C T ∧ (snapshot C t).1 ⊆ nodes (closure C T) := by
  induction t with
  | zero =>
      rw [snapshot_zero]
      constructor
      · rw [← closure_fixed C T]
        exact Or.inl ⟨rfl, rfl⟩
      · intro r hr
        change Fact.node r ∈ closure C T
        rw [← closure_fixed C T]
        exact Or.inl hr
  | succ t ih =>
      obtain ⟨hc, hh⟩ := ih (by omega)
      constructor
      · obtain ⟨G, hg, _⟩ := step_mono (snapshot_step C t) hh
        rw [← closure_fixed C T]
        exact Or.inr ⟨t, (snapshot C t).2, G, by omega, rfl, hc, hg⟩
      · intro r hr
        rcases (step_records (snapshot_step C t) r).mp hr with hold | hnew
        · exact hh hold
        · change Fact.node r ∈ closure C T
          rw [← closure_fixed C T]
          exact Or.inr ⟨t, (snapshot C t).2, by omega, hc, hnew⟩

/-- The positive closure has exactly the bounded computation's
configuration facts and node records, with no spurious configurations. -/
theorem closure_eq_trace (C : Context Γ Λ State Initial) (T : Nat) : closure C T = traceFacts C T := by
  apply Set.Subset.antisymm (closure_sound C T)
  intro fact hf
  cases fact with
  | node r => exact (trace_in_closure C T T (Nat.le_refl T)).2 hf
  | config t c =>
      rcases hf with ⟨ht, rfl⟩
      exact (trace_in_closure C T t ht).1

end Lax751879Proofs.NodeClosure
