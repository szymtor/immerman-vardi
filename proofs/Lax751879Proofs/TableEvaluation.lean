import Lax751879Proofs.Positivity
import Lax751879Proofs.StructureEncoding
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators

-- Preserve Lean 4.30 elaboration of dependent indices during this port.
set_option backward.isDefEq.respectTransparency false

namespace Lax751879Proofs.TableEvaluation

open Lax751879.OrderedStructures Lax751879.FixedPointSyntax
open Lax751879.FixedPointSemantics Lax751879.StructureEncoding
open Lax751879.LeastFixedPoints

/-- A materialized finite relation. Membership tests do not reevaluate the
formula that produced the table. -/
abbrev Table (n k : Nat) := List (Fin k → Fin n)

abbrev TableEnv (n : Nat) (ρ : List Nat) :=
  (r : Fin ρ.length) → Table n (ρ.get r)

def denote {n : Nat} {ρ : List Nat} (η : TableEnv n ρ) : RelationEnv n ρ :=
  fun r => {a | a ∈ η r}

def rounds {α : Type} (next : List α → List α) : Nat → List α
  | 0 => []
  | t + 1 => next (rounds next t)

/-- An executable evaluator. Every fixed-point round explicitly stores its
result table before the next round begins. -/
def evaluate {σ : Vocabulary} {m : Nat} {ρ : List Nat}
    (φ : RawFormula σ m ρ) (A : OrderedStructure σ)
    (v : Fin m → Fin A.size) (η : TableEnv A.size ρ) : Bool :=
  match φ with
  | .truth => true
  | .equal x y => decide (v x = v y)
  | .less x y => decide (v x < v y)
  | .relation r args => A.relation r (v ∘ args)
  | .variable r args => decide ((v ∘ args) ∈ η r)
  | .neg ψ => !(evaluate ψ A v η)
  | .conj ψ χ => evaluate ψ A v η && evaluate χ A v η
  | .exists' ψ => (List.finRange A.size).any fun a =>
      evaluate ψ A (Fin.cons a v) η
  | .lfp k body args =>
      let next := fun R => (tuples A.size k).filter fun a =>
        evaluate body A (Fin.append a v) (Fin.cons R η)
      decide ((v ∘ args) ∈ rounds next (A.size ^ k))

theorem denote_cons {n k : Nat} {ρ : List Nat} (R : Table n k)
    (η : TableEnv n ρ) :
    denote (Fin.cons R η) = extend {a | a ∈ R} (denote η) := by
  funext r
  exact Fin.cases rfl (fun _ => rfl) r

theorem rounds_correct {α : Type} (next : List α → List α)
    (F : Set α → Set α)
    (h : ∀ R, {a | a ∈ next R} = F {a | a ∈ R}) (t : Nat) :
    {a | a ∈ rounds next t} = stage F t := by
  induction t with
  | zero => simp [rounds, stage]
  | succ t ih => rw [rounds, h, ih, stage]

theorem evaluate_correct {σ : Vocabulary} {m : Nat} {ρ : List Nat}
    (φ : RawFormula σ m ρ) (hφ : φ.Admissible) (A : OrderedStructure σ)
    (v : Fin m → Fin A.size) (η : TableEnv A.size ρ) :
    evaluate φ A v η = true ↔ eval φ A v (denote η) := by
  induction φ with
  | truth => simp [evaluate, eval]
  | equal x y => simp [evaluate, eval]
  | less x y => simp [evaluate, eval]
  | relation r args => rfl
  | «variable» r args =>
      simp only [evaluate, eval, denote, decide_eq_true_eq]
      rfl
  | neg ψ ih => simpa [evaluate, eval] using not_congr (ih hφ v η)
  | conj ψ χ ihψ ihχ =>
      simp only [evaluate, Bool.and_eq_true, eval]
      exact and_congr (ihψ hφ.1 v η) (ihχ hφ.2 v η)
  | exists' ψ ih =>
      simp only [evaluate, List.any_eq_true, List.mem_finRange, true_and, eval]
      exact exists_congr (fun a => ih hφ (Fin.cons a v) η)
  | lfp k body args ih =>
      let next := fun R => (tuples A.size k).filter fun a =>
        evaluate body A (Fin.append a v) (Fin.cons R η)
      let F := bodyOperator body A v (denote η)
      have hnext : ∀ R, {a | a ∈ next R} = F {a | a ∈ R} := by
        intro R
        apply Set.ext
        intro a
        simp only [next, List.mem_filter, StructureEncoding.mem_tuples, true_and]
        change evaluate body A (Fin.append a v) (Fin.cons R η) = true ↔
          eval body A (Fin.append a v) (extend {a | a ∈ R} (denote η))
        exact (ih hφ.1 (Fin.append a v) (Fin.cons R η)).trans
          (iff_of_eq (congrArg (eval body A (Fin.append a v)) (denote_cons R η)))
      have hrounds : {a | a ∈ rounds next (A.size ^ k)} = leastFixedPoint F := by
        rw [rounds_correct next F hnext]
        have hmono := Positivity.positiveBodyMonotone body hφ.1 hφ.2 A v (denote η)
        simpa only [Fintype.card_fun, Fintype.card_fin] using
          LeastFixedPoints.finiteConvergence F hmono
      change decide ((v ∘ args) ∈ rounds next (A.size ^ k)) = true ↔
        (v ∘ args) ∈ leastFixedPoint F
      rw [decide_eq_true_eq, ← hrounds]
      rfl

end Lax751879Proofs.TableEvaluation
