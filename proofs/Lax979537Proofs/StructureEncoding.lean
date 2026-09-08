import Lax979537.StructureEncoding
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Lean.Elab.Tactic.Omega

namespace Lax979537Proofs.StructureEncoding

open Lax979537.OrderedStructures Lax979537.StructureEncoding

theorem tuples_length (n k : Nat) : (tuples n k).length = n ^ k := by
  induction k with
  | zero => simp [tuples]
  | succ k ih =>
      simp [tuples, List.length_flatMap, ih, List.sum_replicate,
        Nat.pow_succ, Nat.mul_comm]

theorem mem_tuples (n k : Nat) (a : Fin k → Fin n) : a ∈ tuples n k := by
  induction k with
  | zero =>
      have h : a = Fin.elim0 := Subsingleton.elim _ _
      simp [tuples, h]
  | succ k ih =>
      apply List.mem_flatMap.mpr
      refine ⟨a 0, by simp, ?_⟩
      exact List.mem_map.mpr ⟨Fin.tail a, ih _, Fin.cons_self_tail a⟩

theorem unary_length (n : Nat) : (unary n).length = n + 1 := by
  simp [unary]

theorem map_get_finRange (σ : Vocabulary) (f : Nat → Nat) :
    ((List.finRange σ.length).map fun r => f (σ.get r)) = σ.map f := by
  change List.map (f ∘ σ.get) (List.finRange σ.length) = σ.map f
  rw [← List.map_map, List.map_get_finRange]

/--
---
conclusion: Lax979537.StructureEncoding.encodeLength
---
-/
theorem encodeLength {σ : Vocabulary} {k : Nat} (A : PointedStructure σ k) :
    (encode A).length = A.structureValue.size + 1 +
      (σ.map (fun r => A.structureValue.size ^ r)).sum +
      ((List.finRange k).map (fun i => (A.tuple i).val + 1)).sum := by
  simp only [encode, List.length_append, unary_length, List.length_flatMap,
    List.length_map, tuples_length, map_get_finRange]

/-- A unary code is self-delimiting even with an arbitrary suffix. -/
theorem unary_append_inj (n m : Nat) (xs ys : List Bool)
    (h : unary n ++ xs = unary m ++ ys) : n = m ∧ xs = ys := by
  induction n generalizing m with
  | zero =>
      cases m with
      | zero => simpa [unary] using h
      | succ m => simp [unary, List.replicate_succ] at h
  | succ n ih =>
      cases m with
      | zero => simp [unary, List.replicate_succ] at h
      | succ m =>
          have h' : unary n ++ xs = unary m ++ ys := by
            simpa [unary, List.replicate_succ] using h
          obtain ⟨hn, ht⟩ := ih m h'
          exact ⟨congrArg Nat.succ hn, ht⟩

/-- Fixed-length blocks can be recovered individually from their concatenation. -/
theorem blocks_append_inj {ι : Type} (is : List ι) (f g : ι → List Bool)
    (xs ys : List Bool) (hlen : ∀ i ∈ is, (f i).length = (g i).length)
    (h : is.flatMap f ++ xs = is.flatMap g ++ ys) :
    (∀ i ∈ is, f i = g i) ∧ xs = ys := by
  induction is with
  | nil => simpa using h
  | cons i is ih =>
      simp only [List.flatMap_cons, List.append_assoc] at h
      obtain ⟨hi, ht⟩ := List.append_inj h (hlen i (by simp))
      obtain ⟨hrest, htail⟩ := ih (fun j hj => hlen j (by simp [hj])) ht
      refine ⟨?_, htail⟩
      intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact hi
      · exact hrest j hj

theorem unary_blocks_inj {ι : Type} (is : List ι) (f g : ι → Nat)
    (h : is.flatMap (fun i => unary (f i)) =
      is.flatMap (fun i => unary (g i))) : ∀ i ∈ is, f i = g i := by
  induction is with
  | nil => simp
  | cons i is ih =>
      obtain ⟨hi, ht⟩ := unary_append_inj (f i) (g i) _ _ h
      intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact hi
      · exact ih ht j hj

/--
---
conclusion: Lax979537.StructureEncoding.encodeInjective
---
-/
theorem encodeInjective (σ : Vocabulary) (k : Nat) :
    Function.Injective (@encode σ k) := by
  rintro ⟨⟨n, R⟩, a⟩ ⟨⟨m, S⟩, b⟩ h
  change (unary n ++ _) ++ _ = (unary m ++ _) ++ _ at h
  rw [List.append_assoc, List.append_assoc] at h
  obtain ⟨hn, hrest⟩ := unary_append_inj n m _ _ h
  cases hn
  obtain ⟨hR, ha⟩ := blocks_append_inj (List.finRange σ.length)
    (fun r => (tuples n (σ.get r)).map (R r))
    (fun r => (tuples n (σ.get r)).map (S r)) _ _ (by simp) hrest
  have hRS : R = S := by
    funext r t
    exact List.map_inj_left.mp (hR r (by simp)) t (mem_tuples _ _ t)
  cases hRS
  have hab : a = b := by
    funext i
    apply Fin.ext
    exact unary_blocks_inj (List.finRange k) (fun i => (a i).val)
      (fun i => (b i).val) ha i (by simp)
  cases hab
  rfl

end Lax979537Proofs.StructureEncoding
