import Lax751879Proofs.FormulaCorrectness
import Lax751879Proofs.LfpWorkspace

namespace Lax751879Proofs.FormulaProgram

open Lax751879.OrderedStructures Lax751879.FixedPointSyntax StackBoolean StackTuples

variable {K Aux : Type} [DecidableEq K] {σ : Vocabulary} {m k : Nat} {ρ : List Nat}

set_option maxHeartbeats 800000 in
theorem correct_lfp {body : RawFormula σ (k + m) (k :: ρ)}
    (hbody : Correct (K := K) (Aux := Aux) body) (args : Fin k → Fin m) :
    Correct (K := K) (Aux := Aux) (.lfp k body args) := by
  intro input work hs hw A v η s hc hr
  let slots := List.ofFn (fun i => (work (.tupleCounter i), work (.tupleCoordinate i)))
  let pool := List.ofFn (fun i => work (.power i))
  let input' := input.lfpPorts (fun i => work (.tupleCoordinate i)) (work .current)
  let work' := fun p => work (.child p)
  let p := fun R a => TableEvaluation.evaluate body A (Fin.append a v) (Fin.cons R η)
  have hchild : ValidWork input' work' := by
    refine ⟨fun _ _ h => LfpWork.child.inj (hw.1 h), ?_⟩
    intro q
    exact (hw.2 (.child q)).lfpPorts
      (by intro i h; have he := hw.1 h; cases he)
      (by intro h; have he := hw.1 h; cases he)
  have hmap := LfpWork.mapped_ports work
  have hprivate : (work .tmp :: work .rev :: work .current :: work .nextTable :: work .bound ::
      work .counter :: work .stageCoordinate :: (pool ++ ports slots)).Nodup := by
    rw [← hmap]
    exact (List.nodup_map_iff hw.1).mpr LfpWork.privatePorts_nodup
  have hsep : (input.domain :: work .tmp :: work .rev :: work .current :: work .nextTable :: work .bound ::
      work .counter :: work .stageCoordinate :: (pool ++ ports slots)).Nodup := by
    rw [List.nodup_cons]
    refine ⟨?_, hprivate⟩
    rw [← hmap]
    rintro hm
    obtain ⟨w, _, he⟩ := List.mem_map.mp hm
    exact (hw.2 w).1 he
  have hempty : ∀ key, key ∈ work .tmp :: work .rev :: work .current :: work .nextTable :: work .bound ::
      work .counter :: work .stageCoordinate :: (pool ++ ports slots) → s.stk key = [] := by
    intro key hm
    rw [← hmap] at hm
    obtain ⟨w, _, rfl⟩ := List.mem_map.mp hm
    exact hc w
  have hslotsep : (ports slots).Nodup := by
    have h := hprivate
    simp only [List.nodup_cons] at h
    exact (List.nodup_append.mp h.2.2.2.2.2.2.2).2.1
  have hslotfresh (key : K) (hf : ∀ i, key ≠ work (.tupleCounter i) ∧ key ≠ work (.tupleCoordinate i)) :
      key ∉ ports slots := by
    simpa [slots, ports, List.mem_flatMap, List.mem_ofFn] using hf
  obtain ⟨c, hb, hp⟩ := StackLfpArity.evaluate_returns s input.domain (work .tmp) (work .rev)
    (work .current) (work .nextTable) (work .bound) (work .counter) (work .stageCoordinate)
    pool slots hsep hempty k (by simp [slots]) (by simp [pool]) A.size ((costPolynomial body).eval A.size)
    (input.element ∘ args) (v ∘ args)
    (fun i => fresh_element_list work hw.2 [.current, .bound, .counter, .nextTable, .tmp] (args i))
    (fun i => hr.element (args i)) p (compile body input' work') hr.domain (by
      intro i _ R rem scratch a remaining _ bits scratch'
      let running := StackTableStages.running s (work .current) (work .bound) (work .counter)
        (work .stageCoordinate) (@DenseTables.dense A.size k) (A.size ^ k) R i rem scratch
      let base := StackMaterialize.payload running (work .rev)
      let t := packTuple base slots bits (tupleValues a) remaining scratch'
      have hframe (key : K) (hf : ∀ w, key ≠ work w) : t.stk key = s.stk key := by
        rw [show t.stk key = (base bits).stk key from
          packTuple_fresh base slots key (hslotfresh key (fun j => ⟨hf _, hf _⟩)) bits _ _ _]
        simp [base, running, StackMaterialize.payload, StackTableStages.running, StackFor.pack,
          StackTransfer.working, StackStages.prepared, StackTableStages.family, setStack, result, hf]
      have hrOld : Represents input A v η t := by
        apply hr.frame
        intro key hk
        exact hframe key (by intro w he; subst key; exact hk (hw.2 w))
      have hrChild : Represents input' A (Fin.append a v) (Fin.cons R η) t := by
        apply hrOld.lfpPorts
        · intro j
          exact TupleCoordinates.coordinate_ofFn base _ _ hslotsep (fun j => (a j).val) bits remaining scratch' j
        · rw [show t.stk (work .current) = (base bits).stk (work .current) from
            packTuple_fresh base slots (work .current)
              (hslotfresh _ (by intro j; simp [hw.1.eq_iff])) bits _ _ _]
          simp [base, running, StackMaterialize.payload, StackTableStages.running, StackFor.pack,
            StackTransfer.working, StackStages.prepared, StackTableStages.family, setStack, result, hw.1.eq_iff]
      have hcChild : Clean work' t := by
        intro q
        rw [show t.stk (work' q) = (base bits).stk (work' q) from
          packTuple_fresh base slots (work' q)
            (hslotfresh _ (by intro j; simp [work', hw.1.eq_iff])) bits _ _ _]
        simpa [base, running, StackMaterialize.payload, StackTableStages.running, StackFor.pack,
          StackTransfer.working, StackStages.prepared, StackTableStages.family, setStack, result,
          work', hw.1.eq_iff] using hc (.child q)
      exact hbody input' work' (hs.lfpPorts _ _ (Ne.symm (hw.2 .current).1)) hchild
        A (Fin.append a v) (Fin.cons R η) t hcChild hrChild)
  refine ⟨c, ?_, hp⟩
  simpa [costPolynomial, StackLfpValue.eval_costPolynomial, StackLfpTables.costPolynomial,
    StackTableStages.eval_costPolynomial, StackTableStages.roundCost, StackTuples.eval_costPolynomial] using hb

/-- The syntax-directed compiler evaluates every raw formula in polynomial
time. Admissibility is needed only to identify bounded rounds with LFP semantics. -/
theorem compile_correct (φ : RawFormula σ m ρ) : Correct (K := K) (Aux := Aux) φ := by
  induction φ with
  | truth => exact correct_truth
  | equal x y => exact correct_equal x y
  | less x y => exact correct_less x y
  | relation r args => exact correct_relation r args
  | «variable» r args => exact correct_variable r args
  | neg φ ih => exact correct_neg ih
  | conj φ ψ ihφ ihψ => exact correct_conj ihφ ihψ
  | exists' φ ih => exact correct_exists ih
  | lfp k body args ih => exact correct_lfp ih args

end Lax751879Proofs.FormulaProgram
