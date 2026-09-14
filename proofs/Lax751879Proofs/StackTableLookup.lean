import Lax751879Proofs.StackReadBit
import Lax751879Proofs.TupleRank

namespace Lax751879Proofs.StackTableLookup

open StackProgram StackTransfer StackBoolean StackTuples StackHorner TupleRank

variable {K Aux : Type} [DecidableEq K]

def lookup (domain table index counter buffer tmp : K) (coords : List K) : EvalProgram K Aux :=
  .seq (StackIndex.build domain index counter tmp coords) (StackReadBit.readBit table index buffer tmp)

noncomputable def costPolynomial (k : Nat) : Polynomial Nat :=
  StackIndex.costPolynomial k + 12 * Polynomial.X ^ k + 9

theorem eval_costPolynomial (n k : Nat) :
    (costPolynomial k).eval n = StackIndex.budget n k + 12 * n ^ k + 9 := by
  simp [costPolynomial, StackIndex.eval_costPolynomial]

/-- A complete polynomial-time atomic table lookup. It handles repeated
argument ports and nullary tables, returns the selected relation bit, and
restores all inputs and every private workspace stack. -/
theorem lookup_returns (domain table index counter buffer tmp : K)
    (hsep : [domain, table, index, counter, buffer, tmp].Nodup)
    {n k : Nat} (args : Fin k → K) (values : Fin k → Fin n)
    (p : (Fin k → Fin n) → Bool)
    (hfresh : ∀ i, args i ∉ [index, counter, buffer, tmp])
    (s : EvalStore K Aux) (hdomain : s.stk domain = List.replicate n true)
    (htable : s.stk table = (Lax751879.StructureEncoding.tuples n k).map p)
    (hcoords : ∀ i, s.stk (args i) = List.replicate (values i).val true)
    (hindex : s.stk index = []) (hcounter : s.stk counter = [])
    (hbuffer : s.stk buffer = []) (htmp : s.stk tmp = []) :
    ∃ c, c ≤ StackIndex.budget n k + 12 * n ^ k + 9 ∧
      Returns (lookup domain table index counter buffer tmp (List.ofFn args)) s (p values) c := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true,
    not_or, and_true] at hsep
  have hbuild : [domain, index, counter, tmp].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true,
      not_or, and_true]
    tauto
  have hread : [table, index, buffer, tmp].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true,
      not_or, and_true]
    tauto
  let val := fun key => (s.stk key).length
  have hval (i : Fin k) : val (args i) = (values i).val := by simp [val, hcoords]
  have hmap : (List.ofFn args).map val = tupleValues values := by
    simp [tupleValues, List.map_ofFn, Function.comp_def, hval]
  obtain ⟨c, hc, hp⟩ := StackIndex.build_executes domain index counter tmp (List.ofFn args) hbuild
    (by
      intro key hm
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hm
      have hf := hfresh i
      simp only [List.mem_cons, List.not_mem_nil, not_false_eq_true, not_or, and_true] at hf ⊢
      tauto)
    n val (by
      intro key hm
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hm
      rw [hval]
      exact Nat.le_of_lt (values i).isLt) 0 s hdomain hindex
    (by
      intro key hm
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hm
      rw [hval, hcoords]) hcounter htmp
  simp only [Nat.zero_add, Nat.one_mul, List.length_ofFn] at hc
  rw [value_eq_rank, hmap] at hp
  let r := rank n (tupleValues values)
  let t := setIndex s index r
  have hbi : buffer ≠ index := by tauto
  have hti : tmp ≠ index := by tauto
  have htablei : table ≠ index := by tauto
  obtain ⟨d, hd, hq⟩ := StackReadBit.readBit_executes table index buffer tmp hread t
    (by simp [t, setIndex, hbi, hbuffer]) (by simp [t, setIndex, hti, htmp])
  have ht : t.stk table = (Lax751879.StructureEncoding.tuples n k).map p := by
    simp [t, setIndex, htablei, htable]
  have hi : t.stk index = List.replicate r true := by simp [t, setIndex]
  rw [ht, hi, List.length_map, StructureEncoding.tuples_length, List.length_replicate] at hd
  rw [ht, hi, List.length_replicate] at hq
  change Executes _ t (setStack (result
    (((Lax751879.StructureEncoding.tuples n k).map p)[rank n (tupleValues values)]?.getD false) t) index []) d at hq
  rw [table_at_rank] at hq
  have he : setStack (result (p values) t) index [] = result (p values) s := by
    simp [setStack, result, t, setIndex, Function.update_idem, ← hindex]
  change Executes _ t (setStack (result (p values) t) index []) d at hq
  rw [he] at hq
  have hr : r < n ^ k := rank_lt n k values
  exact ⟨c + d, by omega, Executes.seq hp hq⟩

end Lax751879Proofs.StackTableLookup
