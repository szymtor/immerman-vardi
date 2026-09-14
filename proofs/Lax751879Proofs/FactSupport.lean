import Lax751879Proofs.NodeSupport

namespace Lax751879Proofs.FactSupport

open Turing TimedNodes NodeTrace NodeClosure NodeSupport

variable {Initial : Type}

theorem before_mono {s t : Nat} (hst : s ≤ t) {n : TimedNodes.Node Initial} (h : Before s n) :
    Before t n := by
  cases n with
  | inl => trivial
  | inr n => exact h.trans_le hst

theorem within_mono {s t : Nat} (hst : s ≤ t) {p : Option (TimedNodes.Node Initial)}
    (h : Within s p) : Within t p := fun n hn => before_mono hst (h n hn)

def Valid (tm : FinTM2) (B : Nat) : Fact tm.Γ tm.Λ tm.σ Initial → Prop
  | .config t c => t < B ∧ c.cursor ∈ TM2MicroSupport.controls tm ∧ ∀ k, Within B (c.heads k)
  | .node (n, a, parent) => Before B n ∧ a ∈ TM2Alphabet.alphabet tm ∧ Within B parent

/-- The whole positive closure lies in the supported, bounded part of the
raw Fact type. This includes retained records and every configuration head. -/
theorem closure_valid (tm : FinTM2) (xs : List (tm.Γ tm.k₀)) (ids : Fin xs.length → Initial)
    (hi : Function.Injective ids) (T : Nat) (fact : Fact tm.Γ tm.Λ tm.σ Initial)
    (hf : fact ∈ closure (input tm xs ids hi) T) : Valid tm (T + 1) fact := by
  rw [closure_eq_trace] at hf
  cases fact with
  | config t c =>
      rcases hf with ⟨ht, rfl⟩
      exact ⟨by omega, snapshot_control tm xs ids hi t,
        fun k => within_mono (by omega : t ≤ T + 1) (snapshot_heads_within tm xs ids hi t k)⟩
  | node r =>
      rcases r with ⟨n, a, parent⟩
      obtain ⟨hn, ha, hp⟩ := snapshot_record_support tm xs ids hi T n a parent hf
      exact ⟨before_mono (Nat.le_succ T) hn, ha, within_mono (Nat.le_succ T) hp⟩

end Lax751879Proofs.FactSupport
