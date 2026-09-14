import Lax751879.FixedPointSemantics
import Lax751879Proofs.LeastFixedPoints

namespace Lax751879Proofs.Positivity

open Lax751879.OrderedStructures Lax751879.FixedPointSyntax
open Lax751879.FixedPointSemantics Lax751879.LeastFixedPoints

def Varies {α : Type} (p : Bool) (R S : Set α) : Prop :=
  if p then R ⊆ S else S ⊆ R

theorem varies_reverse {α : Type} (p : Bool) (R S : Set α) :
    Varies p R S → Varies (!p) S R := by
  cases p <;> simp [Varies]

/-- Positivity controls dependence on a free relation variable even under
negation and nested fixed-point binders. -/
theorem eval_variance {σ : Vocabulary} {m : Nat} {ρ : List Nat}
    (φ : RawFormula σ m ρ) (A : OrderedStructure σ)
    (r : Fin ρ.length) (p : Bool) (hp : φ.positiveAt r p)
    (v : Fin m → Fin A.size) (η ζ : RelationEnv A.size ρ)
    (heq : ∀ s, s ≠ r → η s = ζ s) (hvar : Varies p (η r) (ζ r)) :
    eval φ A v η → eval φ A v ζ := by
  induction φ generalizing p with
  | truth => exact id
  | equal x y => exact id
  | less x y => exact id
  | relation s args => exact id
  | «variable» s args =>
      by_cases hs : s = r
      · subst s
        have hpos : p = true := hp rfl
        subst p
        exact fun h => hvar h
      · simpa only [eval, heq s hs] using (id : ζ s (v ∘ args) → ζ s (v ∘ args))
  | neg ψ ih =>
      intro hn hy
      apply hn
      exact ih r (!p) hp v ζ η (fun s hs => (heq s hs).symm)
        (varies_reverse p _ _ hvar) hy
  | conj ψ χ ihψ ihχ =>
      intro h
      exact ⟨ihψ r p hp.1 v η ζ heq hvar h.1,
        ihχ r p hp.2 v η ζ heq hvar h.2⟩
  | exists' ψ ih =>
      rintro ⟨a, ha⟩
      exact ⟨a, ih r p hp (Fin.cons a v) η ζ heq hvar ha⟩
  | lfp k body args ih =>
      apply LeastFixedPoints.lfp_mono
      intro R a ha
      apply ih r.succ p hp (Fin.append a v) (extend R η) (extend R ζ)
        _ hvar ha
      intro s hs
      refine Fin.cases ?_ (fun t ht => ?_) s hs
      · intro _
        rfl
      · exact heq t (fun h => ht (congrArg Fin.succ h))

/--
---
conclusion: Lax751879.FixedPointSemantics.positiveBodyMonotone
---
-/
theorem positiveBodyMonotone {σ : Vocabulary} {m k : Nat} {ρ : List Nat}
    (body : RawFormula σ (k + m) (k :: ρ))
    (_hbody : body.Admissible) (hpositive : body.positiveAt 0 true)
    (A : OrderedStructure σ) (v : Fin m → Fin A.size)
    (η : RelationEnv A.size ρ) : Monotone (bodyOperator body A v η) := by
  intro R S hRS a ha
  apply eval_variance body A 0 true hpositive (Fin.append a v)
    (extend R η) (extend S η) _ hRS ha
  intro s hs
  refine Fin.cases ?_ (fun _ _ => rfl) s hs
  exact fun h => False.elim (h rfl)

end Lax751879Proofs.Positivity
