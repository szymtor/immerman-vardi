import Lax751879Proofs.AddressFormulas
import Mathlib.Data.Fintype.EquivFin

namespace Lax751879Proofs.TupleCoding

open Lax751879.OrderedStructures Lax751879.FixedPointSyntax
open Lax751879.FixedPointSemantics

def pad {n k w : Nat} (zero : Fin n) (x : Fin k → Fin n) : Fin w → Fin n :=
  fun i => if h : i.val < k then x ⟨i.val, h⟩ else zero

theorem pad_get {n k w : Nat} (zero : Fin n) (x : Fin k → Fin n) (h : k ≤ w) (i : Fin k) :
    pad (w := w) zero x (Fin.castLE h i) = x i := by simp [pad, i.isLt]

theorem pad_injective {n k w : Nat} (zero : Fin n) (h : k ≤ w) :
    Function.Injective (pad (n := n) (k := k) (w := w) zero) := by
  intro x y he
  funext i
  simpa only [pad_get] using congrFun he (Fin.castLE h i)

noncomputable def finiteTag {α : Type} [Fintype α] (a : α) : Nat :=
  (Fintype.equivFin α a).val

theorem finiteTag_lt {α : Type} [Fintype α] (a : α) : finiteTag a < Fintype.card α :=
  (Fintype.equivFin α a).isLt

theorem finiteTag_injective {α : Type} [Fintype α] : Function.Injective (finiteTag (α := α)) := by
  intro a b h
  exact (Fintype.equivFin α).injective (Fin.ext h)

noncomputable def finiteCode {α : Type} [Fintype α] {n : Nat} (hn : Fintype.card α ≤ n) (a : α) : Fin n :=
  ⟨finiteTag a, (finiteTag_lt a).trans_le hn⟩

theorem finiteCode_injective {α : Type} [Fintype α] {n : Nat} (hn : Fintype.card α ≤ n) :
    Function.Injective (finiteCode hn) := fun _ _ h =>
  finiteTag_injective (congrArg (fun x : Fin n => x.val) h)

/-- Finite machine constants become fixed numerals in the logical guards. -/
noncomputable def finiteGuard {σ : Vocabulary} {v : Nat} {ρ : List Nat}
    {α : Type} [Fintype α] (c : α) (x : Fin v) : RawFormula σ v ρ :=
  AddressFormulas.numeral (finiteTag c) x

theorem finiteGuard_firstOrder {σ : Vocabulary} {v : Nat} {ρ : List Nat}
    {α : Type} [Fintype α] (c : α) (x : Fin v) :
    FormulaMacros.FirstOrder (finiteGuard (σ := σ) (ρ := ρ) c x) :=
  AddressFormulas.numeral_firstOrder _ _

theorem eval_finiteGuard {σ : Vocabulary} {v : Nat} {ρ : List Nat}
    {α : Type} [Fintype α] (c : α) (x : Fin v) (A : OrderedStructure σ)
    (hn : Fintype.card α ≤ A.size) (a : Fin v → Fin A.size) (η : RelationEnv A.size ρ) :
    eval (finiteGuard c x) A a η ↔ a x = finiteCode hn c := by
  rw [finiteGuard, AddressFormulas.eval_numeral]
  constructor
  · intro h; apply Fin.ext; exact h
  · intro h; exact congrArg (fun x : Fin A.size => x.val) h

def clock {n d : Nat} (hn : 0 < n) (t : Nat) : Fin d → Fin n :=
  (TupleAddresses.address n d).symm ⟨t % n ^ d, Nat.mod_lt _ (Nat.pow_pos hn)⟩

theorem clock_address {n d : Nat} (hn : 0 < n) (t : Nat) :
    (TupleAddresses.address n d (clock hn t)).val = t % n ^ d := by simp [clock]

theorem clock_injective {n d : Nat} (hn : 0 < n) {s t : Nat}
    (hs : s < n ^ d) (ht : t < n ^ d) (he : clock (d := d) hn s = clock hn t) : s = t := by
  have h := congrArg (fun x => (TupleAddresses.address n d x).val) he
  simpa only [clock_address, Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt ht] using h

def rows {K : Type} {c w n : Nat} (keys : K ≃ Fin c) (f : K → Fin w → Fin n) :
    Fin (c * w) → Fin n :=
  fun i => f (keys.symm (finProdFinEquiv.symm i).1) (finProdFinEquiv.symm i).2

theorem rows_get {K : Type} {c w n : Nat} (keys : K ≃ Fin c) (f : K → Fin w → Fin n)
    (k : K) (j : Fin w) : rows keys f (finProdFinEquiv (keys k, j)) = f k j := by
  simp [rows]

theorem rows_injective {K : Type} {c w n : Nat} (keys : K ≃ Fin c) :
    Function.Injective (rows (w := w) (n := n) keys) := by
  intro f g he
  funext k j
  simpa only [rows_get] using congrFun he (finProdFinEquiv (keys k, j))

theorem append_inj {α : Type} {k m : Nat} {x y : Fin k → α} {u v : Fin m → α}
    (h : Fin.append x u = Fin.append y v) : x = y ∧ u = v := by
  constructor
  · funext i; simpa only [Fin.append_left] using congrFun h (Fin.castAdd m i)
  · funext i; simpa only [Fin.append_right] using congrFun h (Fin.natAdd k i)

end Lax751879Proofs.TupleCoding
