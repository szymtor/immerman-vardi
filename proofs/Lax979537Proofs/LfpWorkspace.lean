import Lax979537Proofs.FormulaRepresentation
import Mathlib.Data.List.Nodup

namespace Lax979537Proofs.FormulaProgram

variable {K Child : Type} {k : Nat}

def LfpWork.slots : List (LfpWork k Child × LfpWork k Child) :=
  List.ofFn (fun i => (.tupleCounter i, .tupleCoordinate i))

def LfpWork.privatePorts : List (LfpWork k Child) :=
  [.tmp, .rev, .current, .nextTable, .bound, .counter, .stageCoordinate] ++
    List.ofFn .power ++ StackTuples.ports LfpWork.slots

theorem LfpWork.mem_slot_ports (w : LfpWork k Child) :
    w ∈ StackTuples.ports LfpWork.slots ↔
      (∃ i, w = .tupleCounter i) ∨ ∃ i, w = .tupleCoordinate i := by
  simp [StackTuples.ports, LfpWork.slots, List.mem_flatMap, List.mem_ofFn, eq_comm, exists_or]

theorem LfpWork.slots_nodup : (StackTuples.ports (LfpWork.slots (k := k) (Child := Child))).Nodup := by
  rw [StackTuples.ports, LfpWork.slots, List.ofFn_eq_map, List.flatMap_map]
  apply List.nodup_flatMap.mpr
  constructor
  · intro i _; simp
  · apply (List.nodup_finRange k).imp
    intro i j hij
    simpa [Function.onFun, List.disjoint_left] using hij

theorem LfpWork.privatePorts_nodup : (LfpWork.privatePorts (k := k) (Child := Child)).Nodup := by
  have hp : (List.ofFn (@LfpWork.power k Child)).Nodup :=
    List.nodup_ofFn.mpr (fun _ _ h => LfpWork.power.inj h)
  have ht := LfpWork.slots_nodup (k := k) (Child := Child)
  simp only [LfpWork.privatePorts, List.nodup_append]
  refine ⟨⟨by simp, hp, ?_⟩, ht, ?_⟩
  · simp [List.mem_ofFn]
  · intro w hw t ht he
    subst t
    rcases (LfpWork.mem_slot_ports w).mp ht with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;>
      simp [List.mem_ofFn] at hw

theorem LfpWork.mapped_ports (work : LfpWork k Child → K) :
    (LfpWork.privatePorts (k := k) (Child := Child)).map work =
      work .tmp :: work .rev :: work .current :: work .nextTable :: work .bound ::
        work .counter :: work .stageCoordinate ::
        (List.ofFn (fun i => work (.power i)) ++ StackTuples.ports
          (List.ofFn (fun i => (work (.tupleCounter i), work (.tupleCoordinate i))))) := by
  simp [LfpWork.privatePorts, LfpWork.slots, StackTuples.ports, List.map_flatMap,
    List.ofFn_eq_map, List.flatMap_map, Function.comp_def]

end Lax979537Proofs.FormulaProgram
