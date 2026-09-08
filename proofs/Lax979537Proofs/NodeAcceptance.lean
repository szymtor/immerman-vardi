import Lax979537Proofs.NodeClosure

namespace Lax979537Proofs.NodeAcceptance

open Turing PersistentStack NodeMachine TimedNodes NodeTrace NodeClosure

variable {K Λ State Initial : Type} {Γ : K → Type} [DecidableEq K]

def accepts (R : Set (Fact Γ Λ State Initial)) (T : Nat) (k : K) (a : Γ k) : Prop :=
  ∃ c parent, Fact.config T c ∈ R ∧ c.cursor = .boundary none ∧
    Read (nodes R) (c.heads k) (some (Sigma.mk k a)) parent

theorem nodes_closure (C : Context Γ Λ State Initial) (T : Nat) :
    nodes (closure C T) = (snapshot C T).1 := by
  rw [closure_eq_trace]
  rfl

/-- The positive node/configuration closure accepts exactly the symbol
returned by the actual bounded TM2 computation. Initial identifiers are
arbitrary distinct names, to be instantiated by the FO input interpretation. -/
theorem accepts_iff (tm : FinTM2) (xs : List (tm.Γ tm.k₀)) (ids : Fin xs.length → Initial)
    (hi : Function.Injective ids) (answer a : tm.Γ tm.k₁) {T N : Nat}
    (h : StateTransition.EvalsToInTime tm.step (initList tm xs) (some (haltList tm [answer])) T)
    (hN : TM2Micro.factor tm * T ≤ N) :
    accepts (closure (input tm xs ids hi) N) N tm.k₁ a ↔ a = answer := by
  let C := input tm xs ids hi
  have he := TM2Micro.evals_at_time tm h rfl hN
  have hm := (snapshot_sound C N).2.2
  change Matches (snapshot C N).1 (snapshot C N).2
    ((TM2Micro.next tm.m)^[N] (TM2Micro.boundary (initList tm xs))) at hm
  rw [he] at hm
  have hchain : Chain (snapshot C N).1 ((snapshot C N).2.heads tm.k₁) [Sigma.mk tm.k₁ answer] := by
    simpa [TM2Micro.boundary, haltList] using hm.2.2 tm.k₁
  constructor
  · rintro ⟨c, parent, hc, _, hr⟩
    rw [closure_eq_trace] at hc
    have hce : c = (snapshot C N).2 := hc.2
    rw [hce, nodes_closure] at hr
    have hv := (read_correct (snapshot_sound C N).1 hchain hr).1
    simpa using hv
  · rintro rfl
    obtain ⟨parent, hr, _⟩ := hchain.read_exists
    refine ⟨(snapshot C N).2, parent, (trace_in_closure C N N (Nat.le_refl N)).1, hm.1, ?_⟩
    rw [nodes_closure]
    exact hr

end Lax979537Proofs.NodeAcceptance
