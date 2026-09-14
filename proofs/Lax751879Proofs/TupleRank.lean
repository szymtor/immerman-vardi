import Lax751879Proofs.StackIndex
import Lax751879Proofs.StackTuples
import Lax751879Proofs.TupleAddresses
import Lax751879Proofs.StructureEncoding

namespace Lax751879Proofs.TupleRank

open StackTuples TupleAddresses

def rank (n : Nat) (values : List Nat) : Nat := values.foldl (fun a v => n * a + v) 0

def weighted (n : Nat) : List Nat → Nat
  | [] => 0
  | v :: values => v * n ^ values.length + weighted n values

theorem fold_horner (n a : Nat) (values : List Nat) :
    values.foldl (fun a v => n * a + v) a = a * n ^ values.length + weighted n values := by
  induction values generalizing a with
  | nil => simp [weighted]
  | cons v values ih =>
      rw [List.foldl_cons, ih]
      simp only [List.length_cons, weighted, pow_succ]
      ring

theorem tupleValues_length {n k : Nat} (v : Fin k → Fin n) : (tupleValues v).length = k := by
  simp [tupleValues]

theorem tupleValues_succ {n k : Nat} (v : Fin (k + 1) → Fin n) :
    tupleValues v = (v 0).val :: tupleValues (Fin.tail v) := by
  simp [tupleValues, List.ofFn_succ, Fin.tail]

theorem weighted_address (n k : Nat) (v : Fin k → Fin n) :
    weighted n (tupleValues v) = (address n k v).val := by
  induction k with
  | zero =>
      have h := (address n 0 v).isLt
      simp only [pow_zero] at h
      simp only [tupleValues, List.ofFn_zero, weighted]
      omega
  | succ k ih =>
      rw [tupleValues_succ, weighted, tupleValues_length, ih, address_succ]
      ring

theorem rank_address (n k : Nat) (v : Fin k → Fin n) :
    rank n (tupleValues v) = (address n k v).val := by
  simp only [rank, fold_horner, Nat.zero_mul, Nat.zero_add]
  exact weighted_address n k v

theorem value_eq_rank {K : Type} (n : Nat) (coords : List K) (v : K → Nat) :
    StackIndex.value n coords v 0 = rank n (coords.map v) := by
  simp [StackIndex.value, rank, List.foldl_map]

theorem rank_lt (n k : Nat) (v : Fin k → Fin n) : rank n (tupleValues v) < n ^ k := by
  rw [rank_address]
  exact (address n k v).isLt

/-- Addressing a concatenation of equal-length blocks. -/
theorem getElem?_blocks {α β : Type} (xs : List α) (f : α → List β) (m : Nat)
    (hlen : ∀ x ∈ xs, (f x).length = m) (i j : Nat) (hj : j < m) :
    (xs.flatMap f)[i * m + j]? = (xs[i]?).bind (fun x => (f x)[j]?) := by
  induction xs generalizing i with
  | nil => simp
  | cons x xs ih =>
      have hx := hlen x (by simp)
      have ht : ∀ x ∈ xs, (f x).length = m := fun x hm => hlen x (by simp [hm])
      cases i with
      | zero =>
          simp only [Nat.zero_mul, Nat.zero_add, List.flatMap_cons, List.getElem?_cons_zero,
            Option.bind_some]
          exact List.getElem?_append_left (by omega)
      | succ i =>
          rw [List.flatMap_cons, List.getElem?_append_right (by rw [hx, Nat.succ_mul]; omega)]
          have he : (i + 1) * m + j - (f x).length = i * m + j := by rw [hx, Nat.succ_mul]; omega
          rw [he, ih ht]
          rfl

/-- A tuple's numerical address selects exactly that tuple from the
canonical encoding enumeration, without a sorting or permutation assumption. -/
theorem canonical_at_address (n k : Nat) (v : Fin k → Fin n) :
    (Lax751879.StructureEncoding.tuples n k)[(address n k v).val]? = some v := by
  induction k with
  | zero =>
      have hz : (address n 0 v).val = 0 := by
        have h := (address n 0 v).isLt
        simp only [pow_zero] at h
        omega
      rw [hz]
      have hv : v = Fin.elim0 := Subsingleton.elim _ _
      simp [Lax751879.StructureEncoding.tuples, hv]
  | succ k ih =>
      rw [Lax751879.StructureEncoding.tuples, address_succ]
      have he : (address n k (Fin.tail v)).val + n ^ k * (v 0).val =
          (v 0).val * n ^ k + (address n k (Fin.tail v)).val := by ring
      rw [he, getElem?_blocks (List.finRange n)
        (fun (a : Fin n) => (Lax751879.StructureEncoding.tuples n k).map
          (fun (t : Fin k → Fin n) => (Fin.cons a t : Fin (k + 1) → Fin n))) (n ^ k)
        (by intro a ha; simp [StructureEncoding.tuples_length]) (v 0).val
        (address n k (Fin.tail v)).val (address n k (Fin.tail v)).isLt]
      have hget : (List.finRange n)[(v 0).val]? = some (v 0) := by simp
      rw [hget]
      simp only [Option.bind_some, List.getElem?_map, ih]
      simp [Fin.cons_self_tail]

theorem table_at_rank {n k : Nat} (p : (Fin k → Fin n) → Bool) (v : Fin k → Fin n) :
    ((Lax751879.StructureEncoding.tuples n k).map p)[rank n (tupleValues v)]? = some (p v) := by
  rw [rank_address, List.getElem?_map, canonical_at_address]
  rfl

end Lax751879Proofs.TupleRank
