import Mathlib.Algebra.Polynomial.Eval.Defs
import Lean.Elab.Tactic.Omega

namespace Lax979537Proofs.PolynomialBounds

open Polynomial

theorem eval_mono (p : Polynomial Nat) {n m : Nat} (h : n ≤ m) :
    p.eval n ≤ p.eval m := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [eval_add] using Nat.add_le_add hp hq
  | monomial d c =>
      simpa only [eval_monomial] using
        Nat.mul_le_mul_left c (Nat.pow_le_pow_left h d)

/-- A single power of the domain size absorbs every fixed polynomial and
its constants, uniformly for domains with at least two elements. -/
theorem exists_power (p : Polynomial Nat) :
    ∃ k : Nat, ∀ n : Nat, 2 ≤ n → p.eval n < n ^ k := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      obtain ⟨i, hi⟩ := hp
      obtain ⟨j, hj⟩ := hq
      refine ⟨i + j + 1, fun n hn => ?_⟩
      have hn1 : 1 ≤ n := by omega
      have hpi := hi n hn
      have hqj := hj n hn
      have hni : n ^ i ≤ n ^ (i + j) := Nat.pow_le_pow_right hn1 (by omega)
      have hnj : n ^ j ≤ n ^ (i + j) := Nat.pow_le_pow_right hn1 (by omega)
      calc
        (p + q).eval n = p.eval n + q.eval n := eval_add
        _ < n ^ (i + j) + n ^ (i + j) := Nat.add_lt_add (hpi.trans_le hni) (hqj.trans_le hnj)
        _ = n ^ (i + j) * 2 := by omega
        _ ≤ n ^ (i + j) * n := Nat.mul_le_mul_left _ hn
        _ = n ^ (i + j + 1) := (pow_succ _ _).symm
  | monomial d c =>
      refine ⟨c + 1 + d, fun n hn => ?_⟩
      have hc : c < n ^ (c + 1) :=
        (Nat.lt_succ_self c).trans_le
          ((Nat.le_of_lt (Nat.lt_two_pow_self (n := c + 1))).trans
            (Nat.pow_le_pow_left hn (c + 1)))
      simpa only [eval_monomial, pow_add] using
        Nat.mul_lt_mul_of_pos_right hc (Nat.pow_pos (by omega : 0 < n))

end Lax979537Proofs.PolynomialBounds
