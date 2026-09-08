import Lax979537Proofs.NodeMachine

namespace Lax979537Proofs.TimedNodes

open Turing PersistentStack NodeMachine

variable {K Λ State Initial : Type} {Γ : K → Type} [DecidableEq K]

abbrev Node (Initial : Type) := Initial ⊕ Nat

def Before (t : Nat) : Node Initial → Prop
  | .inl _ => True
  | .inr u => u < t

def Bounded (H : Records (Node Initial) Γ) (t : Nat) : Prop :=
  ∀ n a p, (n, a, p) ∈ H → Before t n

omit [DecidableEq K] in
theorem bounded_mono {H : Records (Node Initial) Γ} {t u : Nat} (h : Bounded H t) (htu : t ≤ u) :
    Bounded H u := by
  intro n a p hn
  have hb := h n a p hn
  cases n with
  | inl i => trivial
  | inr v => exact Nat.lt_of_lt_of_le hb htu

omit [DecidableEq K] in
theorem bounded_fresh {H : Records (Node Initial) Γ} {t : Nat} (h : Bounded H t) : Fresh H (.inr t) := by
  intro a p hm
  exact Nat.lt_irrefl t (h (.inr t) a p hm)

theorem step_bounded {M : Λ → TM2.Stmt Γ Λ State} {t : Nat} {H G : Records (Node Initial) Γ}
    {c d : NodeMachine.Cfg Γ Λ State (Node Initial)} (h : Step M (.inr t) H c G d) (hH : Bounded H t) :
    Bounded G (t + 1) := by
  have hm := bounded_mono hH (Nat.le_succ t)
  cases h with
  | push k f q v heads =>
      intro n a p hn
      rcases Set.mem_insert_iff.mp hn with he | hn
      · cases he; exact Nat.lt_succ_self t
      · exact hm n a p hn
  | stopped | enter | pop | peek | load | branch | goto | halt => exact hm

/-- The node allocated by a push is indexed by its unique microstep time. -/
inductive Run (M : Λ → TM2.Stmt Γ Λ State) (H₀ : Records (Node Initial) Γ)
    (c₀ : NodeMachine.Cfg Γ Λ State (Node Initial)) :
    Nat → Records (Node Initial) Γ → NodeMachine.Cfg Γ Λ State (Node Initial) → Prop
  | zero : Run M H₀ c₀ 0 H₀ c₀
  | succ {t H c G d} : Run M H₀ c₀ t H c → Step M (.inr t) H c G d → Run M H₀ c₀ (t + 1) G d

theorem run_sound {M : Λ → TM2.Stmt Γ Λ State} {H₀ H : Records (Node Initial) Γ}
    {c₀ c : NodeMachine.Cfg Γ Λ State (Node Initial)} {t : Nat}
    (h : Run M H₀ c₀ t H c) (hF : Functional H₀) (hB : Bounded H₀ 0)
    (d₀ : TM2Micro.Cfg Γ Λ State) (hM : Matches H₀ c₀ d₀) :
    Functional H ∧ Bounded H t ∧ Matches H c ((TM2Micro.next M)^[t] d₀) := by
  induction h with
  | zero => exact ⟨hF, hB, hM⟩
  | @succ t H c G d hr hs ih =>
      obtain ⟨hG, hmatch⟩ := step_sound hs ih.1 (bounded_fresh ih.2.1)
        ((TM2Micro.next M)^[t] d₀).stk ih.2.2.2.2
      rw [ih.2.2.expand_eq] at hmatch
      refine ⟨hG, step_bounded hs ih.2.1, ?_⟩
      simpa only [Function.iterate_succ_apply'] using hmatch

theorem run_exists (M : Λ → TM2.Stmt Γ Λ State) (H₀ : Records (Node Initial) Γ)
    (c₀ : NodeMachine.Cfg Γ Λ State (Node Initial)) (hF : Functional H₀) (hB : Bounded H₀ 0)
    (d₀ : TM2Micro.Cfg Γ Λ State) (hM : Matches H₀ c₀ d₀) (t : Nat) :
    ∃ H c, Run M H₀ c₀ t H c := by
  induction t with
  | zero => exact ⟨H₀, c₀, .zero⟩
  | succ t ih =>
      obtain ⟨H, c, hr⟩ := ih
      have hmatch := (run_sound hr hF hB d₀ hM).2.2
      obtain ⟨G, d, hs⟩ := step_exists M (.inr t) H c ((TM2Micro.next M)^[t] d₀).stk hmatch.2.2
      exact ⟨G, d, .succ hr hs⟩

theorem run_unique {M : Λ → TM2.Stmt Γ Λ State} {H₀ H G : Records (Node Initial) Γ}
    {c₀ c d : NodeMachine.Cfg Γ Λ State (Node Initial)} {t : Nat}
    (hF : Functional H₀) (hB : Bounded H₀ 0) (d₀ : TM2Micro.Cfg Γ Λ State) (hM : Matches H₀ c₀ d₀)
    (hc : Run M H₀ c₀ t H c) (hd : Run M H₀ c₀ t G d) : H = G ∧ c = d := by
  induction hc generalizing G d with
  | zero => cases hd; exact ⟨rfl, rfl⟩
  | @succ t H c J e hr hs ih =>
      cases hd with
      | succ hr' hs' =>
          obtain ⟨rfl, rfl⟩ := ih hr'
          exact step_unique (run_sound hr hF hB d₀ hM).1 hs hs'

end Lax979537Proofs.TimedNodes
