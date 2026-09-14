import Lax751879Proofs.StructureEncoding
import Mathlib.Algebra.Polynomial.Eval.Defs

namespace Lax751879Proofs.InputSize

open Lax751879.OrderedStructures Lax751879.StructureEncoding
open Polynomial

noncomputable def tablePolynomial : Vocabulary → Polynomial Nat
  | [] => 0
  | r :: σ => X ^ r + tablePolynomial σ

noncomputable def encodingPolynomial (σ : Vocabulary) (k : Nat) : Polynomial Nat :=
  X + 1 + tablePolynomial σ + C k * X

theorem tablePolynomial_eval (σ : Vocabulary) (n : Nat) :
    (tablePolynomial σ).eval n = (σ.map (fun r => n ^ r)).sum := by
  induction σ with
  | nil => simp [tablePolynomial]
  | cons r σ ih => simp [tablePolynomial, ih]

theorem tuple_size_le (n k : Nat) (a : Fin k → Fin n) :
    ((List.finRange k).map (fun i => (a i).val + 1)).sum ≤ k * n := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hi := ih (Fin.tail a)
      have ha := (a 0).isLt
      simp only [List.finRange_succ, List.map_cons, List.map_map, List.sum_cons]
      change (a 0).val + 1 +
        ((List.finRange k).map (fun i => (Fin.tail a i).val + 1)).sum ≤ (k + 1) * n
      rw [Nat.add_mul, Nat.one_mul]
      omega

theorem domain_size_le_encoding {σ : Vocabulary} {k : Nat} (A : PointedStructure σ k) :
    A.structureValue.size + 1 ≤ (encode A).length := by
  rw [StructureEncoding.encodeLength]
  omega

theorem encoding_length_le {σ : Vocabulary} {k : Nat} (A : PointedStructure σ k) :
    (encode A).length ≤ (encodingPolynomial σ k).eval A.structureValue.size := by
  rw [StructureEncoding.encodeLength]
  simp only [encodingPolynomial, eval_add, eval_X, eval_one, eval_mul, eval_C,
    tablePolynomial_eval]
  exact Nat.add_le_add_left (tuple_size_le _ _ A.tuple) _

end Lax751879Proofs.InputSize
