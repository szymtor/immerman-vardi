import Lax979537Proofs.AddressFormulas
import Lax979537Proofs.NodeInput
import Mathlib.Data.List.Pairwise

namespace Lax979537Proofs.SortedLinks

variable {α : Type} (xs : List α) (r : α → Nat)

def First (p : α) : Prop := p ∈ xs ∧ ¬∃ q ∈ xs, r q < r p
def Last (p : α) : Prop := p ∈ xs ∧ ¬∃ q ∈ xs, r p < r q
def Next (p q : α) : Prop :=
  p ∈ xs ∧ q ∈ xs ∧ r p < r q ∧ ¬∃ z ∈ xs, r p < r z ∧ r z < r q

theorem exists_mem_get (P : α → Prop) : (∃ p ∈ xs, P p) ↔ ∃ i : Fin xs.length, P (xs.get i) := by
  constructor
  · rintro ⟨p, hp, h⟩
    obtain ⟨i, rfl⟩ := List.get_of_mem hp
    exact ⟨i, h⟩
  · rintro ⟨i, h⟩
    exact ⟨xs.get i, List.get_mem xs i, h⟩

variable (hs : xs.Pairwise (fun p q => r p < r q))
include hs

theorem strictMono_get : StrictMono (fun i : Fin xs.length => r (xs.get i)) :=
  List.pairwise_iff_get.mp hs

theorem get_lt_iff (i j : Fin xs.length) : r (xs.get i) < r (xs.get j) ↔ i < j :=
  (strictMono_get xs r hs).lt_iff_lt

theorem first_get (i : Fin xs.length) : First xs r (xs.get i) ↔ i.val = 0 := by
  simp only [First, List.get_mem, true_and, exists_mem_get, get_lt_iff xs r hs]
  exact AddressFormulas.no_smaller_iff i

theorem last_get (i : Fin xs.length) : Last xs r (xs.get i) ↔ i.val + 1 = xs.length := by
  simp only [Last, List.get_mem, true_and, exists_mem_get, get_lt_iff xs r hs]
  constructor
  · intro h
    by_contra he
    have hi : i.val + 1 < xs.length := by have := i.isLt; omega
    exact h ⟨⟨i.val + 1, hi⟩, by change i.val < i.val + 1; omega⟩
  · intro h ⟨j, hj⟩
    change i.val < j.val at hj
    have := j.isLt
    omega

theorem next_get (i j : Fin xs.length) : Next xs r (xs.get i) (xs.get j) ↔ i.val + 1 = j.val := by
  simp only [Next, List.get_mem, true_and, exists_mem_get, get_lt_iff xs r hs]
  exact AddressFormulas.no_between_iff i j

theorem first_iff (p : α) : First xs r p ↔ ∃ i : Fin xs.length, xs.get i = p ∧ i.val = 0 := by
  constructor
  · intro h
    obtain ⟨i, rfl⟩ := List.get_of_mem h.1
    exact ⟨i, rfl, (first_get xs r hs i).mp h⟩
  · rintro ⟨i, rfl, hi⟩
    exact (first_get xs r hs i).mpr hi

theorem last_iff (p : α) : Last xs r p ↔
    ∃ i : Fin xs.length, xs.get i = p ∧ i.val + 1 = xs.length := by
  constructor
  · intro h
    obtain ⟨i, rfl⟩ := List.get_of_mem h.1
    exact ⟨i, rfl, (last_get xs r hs i).mp h⟩
  · rintro ⟨i, rfl, hi⟩
    exact (last_get xs r hs i).mpr hi

theorem next_iff (p q : α) : Next xs r p q ↔
    ∃ i j : Fin xs.length, xs.get i = p ∧ xs.get j = q ∧ i.val + 1 = j.val := by
  constructor
  · intro h
    obtain ⟨i, rfl⟩ := List.get_of_mem h.1
    obtain ⟨j, rfl⟩ := List.get_of_mem h.2.1
    exact ⟨i, j, rfl, rfl, (next_get xs r hs i j).mp h⟩
  · rintro ⟨i, j, rfl, rfl, hij⟩
    exact (next_get xs r hs i j).mpr hij

end Lax979537Proofs.SortedLinks
