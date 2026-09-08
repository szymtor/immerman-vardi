import Lax979537.LeastFixedPoints
import Mathlib.Order.FixedPoints
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Finite.Basic
import Lean.Elab.Tactic.Omega

namespace Lax979537Proofs.LeastFixedPoints

open Lax979537.LeastFixedPoints
open scoped Classical

/--
---
conclusion: Lax979537.LeastFixedPoints.least
---
-/
theorem least {α : Type} (F : Set α → Set α) (R : Set α)
    (hR : F R ⊆ R) : leastFixedPoint F ⊆ R :=
  sInf_le hR

/--
---
conclusion: Lax979537.LeastFixedPoints.fixedPoint
---
-/
theorem fixedPoint {α : Type} (F : Set α → Set α) (hF : Monotone F) :
    F (leastFixedPoint F) = leastFixedPoint F :=
  OrderHom.map_lfp ⟨F, hF⟩

theorem lfp_mono {α : Type} {F G : Set α → Set α}
    (h : ∀ R, F R ⊆ G R) : leastFixedPoint F ⊆ leastFixedPoint G :=
  sInf_le_sInf fun R hR => (h R).trans hR

theorem stage_succ {α : Type} (F : Set α → Set α) (hF : Monotone F) :
    ∀ t, stage F t ⊆ stage F (t + 1)
  | 0 => Set.empty_subset _
  | t + 1 => hF (stage_succ F hF t)

theorem stage_le_lfp {α : Type} (F : Set α → Set α) (hF : Monotone F) :
    ∀ t, stage F t ⊆ leastFixedPoint F
  | 0 => Set.empty_subset _
  | t + 1 => by
      rw [stage, ← fixedPoint F hF]
      exact hF (stage_le_lfp F hF t)

theorem stage_fixed {α : Type} (F : Set α → Set α) (hF : Monotone F)
    (t : Nat) (h : stage F (t + 1) = stage F t) :
    stage F t = leastFixedPoint F :=
  Set.Subset.antisymm (stage_le_lfp F hF t) (least F _ h.subset)

theorem cardinal_or_stable {α : Type} [Fintype α]
    (F : Set α → Set α) (hF : Monotone F) (t : Nat) :
    t ≤ (stage F t).toFinset.card ∨ stage F t = leastFixedPoint F := by
  classical
  induction t with
  | zero => exact Or.inl (Nat.zero_le _)
  | succ t ih =>
      by_cases heq : stage F (t + 1) = stage F t
      · exact Or.inr (heq.trans (stage_fixed F hF t heq))
      · rcases ih with hcard | hstable
        · left
          have hsub : (stage F t).toFinset ⊂ (stage F (t + 1)).toFinset := by
            apply Finset.ssubset_iff_subset_ne.mpr
            constructor
            · simpa using stage_succ F hF t
            · intro h
              apply heq
              simpa using congrArg (fun s : Finset α => (s : Set α)) h.symm
          have := Finset.card_lt_card hsub
          omega
        · exact False.elim (heq (by rw [stage, hstable, fixedPoint F hF]))

/--
---
conclusion: Lax979537.LeastFixedPoints.finiteConvergence
---
-/
theorem finiteConvergence {α : Type} [Fintype α]
    (F : Set α → Set α) (hF : Monotone F) :
    stage F (Fintype.card α) = leastFixedPoint F := by
  classical
  rcases cardinal_or_stable F hF (Fintype.card α) with hcard | h
  · have huniv : (stage F (Fintype.card α)).toFinset = Finset.univ := by
      apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      simpa using hcard
    apply Set.Subset.antisymm (stage_le_lfp F hF _)
    have : stage F (Fintype.card α) = Set.univ := by
      simpa using congrArg (fun s : Finset α => (s : Set α)) huniv
    rw [this]
    exact Set.subset_univ _
  · exact h

end Lax979537Proofs.LeastFixedPoints
