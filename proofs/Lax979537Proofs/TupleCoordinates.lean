import Lax979537Proofs.StackTuples

namespace Lax979537Proofs.TupleCoordinates

open StackProgram StackTransfer StackFor StackTuples

variable {K Aux α : Type} [DecidableEq K]

/-- Observe any coordinate installed by tuple traversal. The statement is
uniform in arity and in the surrounding semantic payload and loop counters. -/
theorem coordinate_ofFn (base : α → BitStore K Aux) {k : Nat}
    (counter coord : Fin k → K)
    (hsep : (ports (List.ofFn (fun i => (counter i, coord i)))).Nodup)
    (values : Fin k → Nat) (a : α) (remaining : List Nat) (scratch : Option Bool) (i : Fin k) :
    (packTuple base (List.ofFn (fun i => (counter i, coord i))) a (List.ofFn values) remaining scratch).stk
      (coord i) = List.replicate (values i) true := by
  induction k generalizing base remaining with
  | zero => exact Fin.elim0 i
  | succ k ih =>
      have hs : List.ofFn (fun i => (counter i, coord i)) =
          (counter 0, coord 0) :: List.ofFn (fun j : Fin k => (counter j.succ, coord j.succ)) := by
        rw [List.ofFn_succ]
      have hv : List.ofFn values = values 0 :: List.ofFn (fun j : Fin k => values j.succ) := by
        rw [List.ofFn_succ]
      rw [hs] at hsep ⊢
      rw [hv]
      have hn : counter 0 ≠ coord 0 ∧
          counter 0 ∉ ports (List.ofFn (fun j : Fin k => (counter j.succ, coord j.succ))) ∧
          coord 0 ∉ ports (List.ofFn (fun j : Fin k => (counter j.succ, coord j.succ))) ∧
          (ports (List.ofFn (fun j : Fin k => (counter j.succ, coord j.succ)))).Nodup := by
        simpa only [ports, List.flatMap_cons, List.cons_append, List.nil_append,
          List.nodup_cons, List.mem_cons, not_or, and_assoc] using hsep
      simp only [packTuple, List.headD_cons, List.tail_cons]
      refine Fin.cases ?_ (fun j => ?_) i
      · rw [packTuple_fresh _ _ (coord 0) hn.2.2.1]
        simp [pack, working]
      · exact ih _ (fun j => counter j.succ) (fun j => coord j.succ) hn.2.2.2
          (fun j => values j.succ) remaining.tail j

end Lax979537Proofs.TupleCoordinates
