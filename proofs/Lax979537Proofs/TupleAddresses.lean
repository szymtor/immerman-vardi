import Lax979537Proofs.TupleOrder
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.Pi

namespace Lax979537Proofs.TupleAddresses

open Lax979537.OrderedStructures Lax979537.FixedPointSyntax
open Lax979537.FixedPointSemantics
open TupleOrder

/-- Big-endian tuple addresses, matching the lexicographic input encoding. -/
def address (n : Nat) : (k : Nat) → (Fin k → Fin n) ≃ Fin (n ^ k)
  | 0 => (Equiv.ofUnique (Fin 0 → Fin n) (Fin 1)).trans
      (finCongr (Nat.pow_zero n).symm)
  | k + 1 =>
      (Fin.consEquiv (fun _ : Fin (k + 1) => Fin n)).symm |>.trans
        ((Equiv.prodCongr (Equiv.refl _) (address n k)).trans
          (finProdFinEquiv.trans (finCongr (pow_succ' n k).symm)))

theorem address_succ (n k : Nat) (a : Fin (k + 1) → Fin n) :
    (address n (k + 1) a).val = (address n k (Fin.tail a)).val +
      n ^ k * (a 0).val := rfl

theorem lex_succ {n k : Nat} (a b : Fin (k + 1) → Fin n) :
    TupleLex a b ↔ a 0 < b 0 ∨
      (a 0 = b 0 ∧ TupleLex (Fin.tail a) (Fin.tail b)) := by
  constructor
  · rintro ⟨i, hi, hp⟩
    refine Fin.cases ?_ ?_ i hi hp
    · intro hi _
      exact Or.inl hi
    · intro j hi hp
      refine Or.inr ⟨hp 0 (by simp), j, hi, ?_⟩
      intro l hl
      exact hp l.succ (Fin.succ_lt_succ_iff.mpr hl)
  · rintro (h | ⟨h, j, hj, hp⟩)
    · exact ⟨0, h, fun i hi => (Fin.not_lt_zero i hi).elim⟩
    · refine ⟨j.succ, hj, ?_⟩
      intro i
      refine Fin.cases ?_ ?_ i
      · exact fun _ => h
      · intro l hl
        exact hp l (Fin.succ_lt_succ_iff.mp hl)

theorem address_lt_iff (n k : Nat) (a b : Fin k → Fin n) :
    address n k a < address n k b ↔ TupleLex a b := by
  induction k with
  | zero =>
      have he : a = b := Subsingleton.elim _ _
      subst b
      constructor
      · intro h
        exact (Nat.lt_irrefl _ h).elim
      · rintro ⟨i, _, _⟩
        exact Fin.elim0 i
  | succ k ih =>
      rw [lex_succ]
      have ha := (address n k (Fin.tail a)).isLt
      have hb := (address n k (Fin.tail b)).isLt
      change (address n (k + 1) a).val < (address n (k + 1) b).val ↔ _
      rw [address_succ, address_succ]
      rcases lt_trichotomy (a 0) (b 0) with h | h | h
      · have hmul : n ^ k * (a 0).val + n ^ k ≤ n ^ k * (b 0).val := by
          simpa only [Nat.mul_add, Nat.mul_one] using
            Nat.mul_le_mul_left (n ^ k) (Nat.succ_le_of_lt h)
        constructor
        · exact fun _ => Or.inl h
        · intro _
          omega
      · simp only [h, lt_self_iff_false, false_or, true_and,
          Nat.add_lt_add_iff_right]
        exact ih (Fin.tail a) (Fin.tail b)
      · have hmul : n ^ k * (b 0).val + n ^ k ≤ n ^ k * (a 0).val := by
          simpa only [Nat.mul_add, Nat.mul_one] using
            Nat.mul_le_mul_left (n ^ k) (Nat.succ_le_of_lt h)
        constructor
        · intro hh
          omega
        · rintro (hh | ⟨hh, _⟩)
          · exact (lt_asymm h hh).elim
          · exact (ne_of_gt h hh).elim

/-- The already constructed FO tuple comparison is numerical address order. -/
theorem eval_lex_address {σ : Vocabulary} {m k : Nat} {ρ : List Nat}
    (x y : Fin k → Fin m) (A : OrderedStructure σ)
    (v : Fin m → Fin A.size) (η : RelationEnv A.size ρ) :
    eval (lexFormula x y) A v η ↔
      address A.size k (v ∘ x) < address A.size k (v ∘ y) :=
  (eval_lexFormula x y A v η).trans (address_lt_iff _ _ _ _).symm

end Lax979537Proofs.TupleAddresses
