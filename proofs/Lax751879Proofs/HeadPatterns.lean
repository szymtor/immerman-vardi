import Lax751879Proofs.ControlValues

namespace Lax751879Proofs.HeadPatterns

open Turing TupleCoding FactPatterns

variable {tm : FinTM2} {n N w d : Nat}

noncomputable def get (tm : FinTM2) (h : Fin (FactCodes.stackCount tm * (w + 1)) → Fin n)
    (k : tm.K) : Fin (w + 1) → Fin n :=
  fun j => h (finProdFinEquiv (@Fintype.equivFin tm.K tm.kFin k, j))

noncomputable def update (tm : FinTM2) (h : Fin (FactCodes.stackCount tm * (w + 1)) → Fin n)
    (k : tm.K) (p : Fin (w + 1) → Fin n) : Fin (FactCodes.stackCount tm * (w + 1)) → Fin n :=
  rows (@Fintype.equivFin tm.K tm.kFin) (Function.update (get tm h) k p)

theorem map_get (tm : FinTM2) (f : Fin N → Fin n)
    (h : Fin (FactCodes.stackCount tm * (w + 1)) → Fin N) (k : tm.K) :
    f ∘ get tm h k = get tm (f ∘ h) k := rfl

theorem map_update (tm : FinTM2) (f : Fin N → Fin n)
    (h : Fin (FactCodes.stackCount tm * (w + 1)) → Fin N) (k : tm.K) (p : Fin (w + 1) → Fin N) :
    f ∘ update tm h k p = update tm (f ∘ h) k (f ∘ p) := by
  rw [update, map_rows, update]
  congr 1
  funext j
  by_cases hj : j = k
  · subst j; simp only [Function.update_self]
  · simp only [Function.update_of_ne hj, map_get]

theorem get_heads {Initial : Type} {iWidth : Nat}
    (P : FactCodes.Parameters tm Initial n iWidth d w)
    (h : tm.K → Option (TimedNodes.Node Initial)) (k : tm.K) :
    get tm (FactCodes.heads P h) k = NodeCodes.code (d := d) P.enough P.initial (h k) := by
  funext j
  unfold get FactCodes.heads
  exact rows_get _ _ k j

theorem update_heads {Initial : Type} {iWidth : Nat}
    (P : FactCodes.Parameters tm Initial n iWidth d w)
    (h : tm.K → Option (TimedNodes.Node Initial)) (k : tm.K) (p : Option (TimedNodes.Node Initial)) :
    update tm (FactCodes.heads P h) k (NodeCodes.code (d := d) P.enough P.initial p) =
      FactCodes.heads P (Function.update h k p) := by
  unfold update FactCodes.heads
  congr 1
  funext j
  by_cases hj : j = k
  · subst j; simp only [Function.update_self]
  · simp only [Function.update_of_ne hj]
    exact get_heads P h j

/-- The fresh-node pattern has the time-node tag and a padded source clock. -/
def fresh (zero two : Fin n) (time : Fin d → Fin n) : Fin (w + 1) → Fin n :=
  Fin.cons two (pad zero time)

theorem map_fresh (f : Fin N → Fin n) (zero two : Fin N) (time : Fin d → Fin N) :
    f ∘ fresh (w := w) zero two time = fresh (f zero) (f two) (f ∘ time) := by
  simp only [fresh, map_cons, map_pad]

theorem fresh_code {Initial : Type} {iWidth : Nat}
    (P : FactCodes.Parameters tm Initial n iWidth d w) (t : Nat) :
    fresh (w := w) ⟨0, by have := P.enough; omega⟩ ⟨2, by have := P.enough; omega⟩
      (clock (d := d) (by have := P.enough; omega) t) =
      NodeCodes.code (d := d) P.enough P.initial (some (.inr t)) := rfl

end Lax751879Proofs.HeadPatterns
