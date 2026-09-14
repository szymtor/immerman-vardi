import Lax751879Proofs.TableEvaluation
import Lax751879Proofs.InputSize
import Lax751879Proofs.PolynomialBounds

/-!
A deliberately generous polynomial bound for the materialized-table evaluator.
The charge below counts tuple generation, table scans, and recursive evaluation.
It is an algorithmic work bound, not yet a TM2 step bound: the implementation
of these operations on stacks must separately be proved to have polynomial
overhead. In particular this module does not assert `evaluationInP`.
-/

namespace Lax751879Proofs.EvaluationWork

open Lax751879.OrderedStructures Lax751879.FixedPointSyntax
open Lax751879.StructureEncoding
open Lax751879Proofs.TableEvaluation
open Polynomial

def Sized {n : Nat} {ρ : List Nat} (η : TableEnv n ρ) : Prop :=
  ∀ r, (η r).length ≤ n ^ ρ.get r

theorem sized_cons {n k : Nat} {ρ : List Nat} (R : Table n k)
    (η : TableEnv n ρ) (hR : R.length ≤ n ^ k) (hη : Sized η) :
    Sized (ρ := k :: ρ) (Fin.cons R η) := by
  intro r
  exact Fin.cases hR (fun s => hη s) r

def scan (n k length : Nat) : Nat :=
  (k + 1) * (n + 1) * (length + 1)

def roundWork {α : Type} (next : List α → List α) (charge : List α → Nat) :
    Nat → Nat
  | 0 => 0
  | t + 1 => roundWork next charge t + charge (rounds next t)

def work {σ : Vocabulary} {m : Nat} {ρ : List Nat}
    (φ : RawFormula σ m ρ) (A : OrderedStructure σ)
    (v : Fin m → Fin A.size) (η : TableEnv A.size ρ) : Nat :=
  match φ with
  | .truth => 1
  | .equal _ _ | .less _ _ => A.size + 1
  | .relation r _ => scan A.size (σ.get r) (A.size ^ σ.get r)
  | .variable r _ => scan A.size (ρ.get r) (η r).length
  | .neg ψ => 1 + work ψ A v η
  | .conj ψ χ => 1 + work ψ A v η + work χ A v η
  | .exists' ψ => 1 + A.size +
      ((List.finRange A.size).map fun a => work ψ A (Fin.cons a v) η).sum
  | .lfp k body _ =>
      let next := fun R => (tuples A.size k).filter fun a =>
        evaluate body A (Fin.append a v) (Fin.cons R η)
      let charge := fun R => scan A.size k (A.size ^ k) +
        ((tuples A.size k).map fun a =>
          work body A (Fin.append a v) (Fin.cons R η)).sum
      scan A.size k (A.size ^ k) + roundWork next charge (A.size ^ k)

noncomputable def scanPolynomial (k : Nat) : Polynomial Nat :=
  C (k + 1) * (X + 1) * (X ^ k + 1)

/-- The polynomial depends only on the fixed formula, never on its input.
We sum the charges of both branches and all quantified assignments, even
when Boolean short-circuiting would avoid some of them. -/
noncomputable def workPolynomial {σ : Vocabulary} {m : Nat} {ρ : List Nat} :
    RawFormula σ m ρ → Polynomial Nat
  | .truth => 1
  | .equal _ _ | .less _ _ => X + 1
  | .relation r _ => scanPolynomial (σ.get r)
  | .variable r _ => scanPolynomial (ρ.get r)
  | .neg ψ => 1 + workPolynomial ψ
  | .conj ψ χ => 1 + workPolynomial ψ + workPolynomial χ
  | .exists' ψ => 1 + X + X * workPolynomial ψ
  | .lfp k body _ => scanPolynomial k +
      X ^ k * (scanPolynomial k + X ^ k * workPolynomial body)

theorem eval_scanPolynomial (k n : Nat) :
    (scanPolynomial k).eval n = scan n k (n ^ k) := by
  simp [scanPolynomial, scan]

theorem sum_map_le {α : Type} (xs : List α) (f : α → Nat) (B : Nat)
    (h : ∀ a ∈ xs, f a ≤ B) : (xs.map f).sum ≤ xs.length * B := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul,
        Nat.one_mul]
      have ha := h a (by simp)
      have hs := ih (fun b hb => h b (by simp [hb]))
      omega

theorem rounds_sized {n k : Nat} (next : Table n k → Table n k)
    (h : ∀ R, (next R).length ≤ n ^ k) (t : Nat) :
    (rounds next t).length ≤ n ^ k := by
  cases t with
  | zero => simp [rounds]
  | succ t => exact h _

theorem roundWork_le {α : Type} (next : List α → List α)
    (charge : List α → Nat) (B t : Nat)
    (h : ∀ i, i < t → charge (rounds next i) ≤ B) :
    roundWork next charge t ≤ t * B := by
  induction t with
  | zero => simp [roundWork]
  | succ t ih =>
      have hi := ih (fun i hi => h i (by omega))
      have ht := h t (by omega)
      simp only [roundWork, Nat.add_mul, Nat.one_mul]
      omega

theorem work_le {σ : Vocabulary} {m : Nat} {ρ : List Nat}
    (φ : RawFormula σ m ρ) (A : OrderedStructure σ)
    (v : Fin m → Fin A.size) (η : TableEnv A.size ρ) (hη : Sized η) :
    work φ A v η ≤ (workPolynomial φ).eval A.size := by
  induction φ with
  | truth => simp [work, workPolynomial]
  | equal x y => simp [work, workPolynomial]
  | less x y => simp [work, workPolynomial]
  | relation r args => simp [work, workPolynomial, eval_scanPolynomial]
  | «variable» r args =>
      simp only [work, workPolynomial, eval_scanPolynomial, scan]
      exact Nat.mul_le_mul_left _ (Nat.add_le_add_right (hη r) 1)
  | neg ψ ih =>
      simpa only [work, workPolynomial, eval_add, eval_one] using
        Nat.add_le_add_left (ih v η hη) 1
  | conj ψ χ ihψ ihχ =>
      simpa only [work, workPolynomial, eval_add, eval_one] using
        Nat.add_le_add (Nat.add_le_add_left (ihψ v η hη) 1) (ihχ v η hη)
  | exists' ψ ih =>
      simp only [work, workPolynomial, eval_add, eval_one, eval_X, eval_mul]
      apply Nat.add_le_add_left
      simpa only [List.length_finRange] using
        sum_map_le (List.finRange A.size) _ ((workPolynomial ψ).eval A.size)
          (fun a _ => ih (Fin.cons a v) η hη)
  | lfp k body args ih =>
      let next := fun R => (tuples A.size k).filter fun a =>
        evaluate body A (Fin.append a v) (Fin.cons R η)
      have hn : ∀ R, (next R).length ≤ A.size ^ k := by
        intro R
        exact (List.length_filter_le _ _).trans_eq (StructureEncoding.tuples_length _ _)
      simp only [work, workPolynomial, eval_add, eval_mul, eval_pow, eval_X,
        eval_scanPolynomial]
      apply Nat.add_le_add_left
      apply roundWork_le
      intro i _
      apply Nat.add_le_add_left
      simpa only [StructureEncoding.tuples_length] using
        sum_map_le (tuples A.size k) _ ((workPolynomial body).eval A.size)
          (fun a _ => ih (Fin.append a v) (Fin.cons (rounds next i) η)
            (sized_cons _ η (rounds_sized next hn i) hη))

/-- On every encoded pointed structure, the work is bounded by a polynomial
in the actual bit-string length. The empty relation environment is sized. -/
theorem work_le_input_length {σ : Vocabulary} {m : Nat} (φ : Formula σ m)
    (A : PointedStructure σ m) :
    work φ.val A.structureValue A.tuple (fun r => Fin.elim0 r) ≤
      (workPolynomial φ.val).eval (encode A).length := by
  apply (work_le φ.val A.structureValue A.tuple _ (fun r => Fin.elim0 r)).trans
  exact PolynomialBounds.eval_mono _
    (Nat.le_trans (Nat.le_succ _) (InputSize.domain_size_le_encoding A))

end Lax751879Proofs.EvaluationWork
