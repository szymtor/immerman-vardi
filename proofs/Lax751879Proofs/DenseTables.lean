import Lax751879Proofs.StackLfpTables
import Lax751879Proofs.TableEvaluation

namespace Lax751879Proofs.DenseTables

open StackTuples

def dense {n k : Nat} (R : TableEvaluation.Table n k) : List Bool :=
  (Lax751879.StructureEncoding.tuples n k).map (fun v => decide (v ∈ R))

/-- A proof-side extension of a tuple predicate to natural-number lists.
On every valid tuple it is exactly the original predicate. -/
def predicate {n k : Nat} (p : (Fin k → Fin n) → Bool) (values : List Nat) : Bool :=
  (Lax751879.StructureEncoding.tuples n k).any (fun v => decide (tupleValues v = values) && p v)

theorem tupleValues_injective (n k : Nat) : Function.Injective (@tupleValues n k) := by
  intro u v h
  have he := List.ofFn_injective h
  funext i
  exact Fin.ext (congrFun he i)

theorem mem_tuples_iff (n k : Nat) (values : List Nat) :
    values ∈ tuples n k ↔ values.length = k ∧ ∀ i ∈ values, i < n := by
  induction k generalizing values with
  | zero => cases values <;> simp [tuples]
  | succ k ih =>
      cases values with
      | nil => simp [tuples]
      | cons i values =>
          simp [tuples, ih, and_assoc, and_left_comm, and_comm]

theorem valid_values (n k : Nat) (values : List Nat) (hlen : values.length = k)
    (hvalid : ∀ i ∈ values, i < n) :
    ∃ v : Fin k → Fin n, tupleValues v = values := by
  have hm := (mem_tuples_iff n k values).mpr ⟨hlen, hvalid⟩
  rw [tuples_eq_canonical] at hm
  obtain ⟨v, _, hv⟩ := List.mem_map.mp hm
  exact ⟨v, hv⟩

theorem predicate_values {n k : Nat} (p : (Fin k → Fin n) → Bool) (v : Fin k → Fin n) :
    predicate p (tupleValues v) = p v := by
  apply Bool.eq_iff_iff.mpr
  simp only [predicate, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨w, _, he, hp⟩
    exact tupleValues_injective n k he ▸ hp
  · intro hp
    exact ⟨v, StructureEncoding.mem_tuples n k v, rfl, hp⟩

theorem dense_length {n k : Nat} (R : TableEvaluation.Table n k) : (dense R).length = n ^ k := by
  simp [dense, StructureEncoding.tuples_length]

theorem dense_empty (n k : Nat) : dense ([] : TableEvaluation.Table n k) = List.replicate (n ^ k) false := by
  simp [dense, StructureEncoding.tuples_length]

def next {n k : Nat} (p : TableEvaluation.Table n k → (Fin k → Fin n) → Bool)
    (R : TableEvaluation.Table n k) : TableEvaluation.Table n k :=
  (Lax751879.StructureEncoding.tuples n k).filter (p R)

theorem dense_next {n k : Nat} (p : TableEvaluation.Table n k → (Fin k → Fin n) → Bool)
    (R : TableEvaluation.Table n k) :
    dense (next p R) = StackMaterialize.table n k (predicate (p R)) := by
  rw [StackMaterialize.table, tuples_eq_canonical, List.map_map]
  apply List.map_congr_left
  intro v hv
  simp [next, hv, predicate_values]

theorem rounds_eq_iterate {β : Type} (f : List β → List β) (t : Nat) :
    TableEvaluation.rounds f t = (f^[t]) [] := by
  induction t with
  | zero => rfl
  | succ t ih => simp [TableEvaluation.rounds, ih, Function.iterate_succ_apply']

end Lax751879Proofs.DenseTables
