import Lax979537Proofs.PushRules
import Lax979537Proofs.PushValues
import Lax979537Proofs.PlainClosure

namespace Lax979537Proofs.PushClosure

open Turing Lax979537.OrderedStructures
open NodeClosure TupleCoding

variable {f : List Bool → Bool} (h : TM2ComputableInPolyTime id (fun b : Bool => [b]) f)
    {σ : Vocabulary} {m : Nat} (d : Nat) (A : PointedStructure σ m)
    (hn : TraceCodes.threshold h.tm σ m ≤ A.structureValue.size)

/-- Both finite push rule families preserve the encoded canonical trace:
the configuration update and the separately emitted immutable record. -/
theorem preserves (emit : Bool) :
    ParameterizedRules.operator (PushRules.rules h.tm σ m d (TraceCodes.nodeWidth σ d) emit)
      A.structureValue A.tuple (TraceCodes.encoded h d A hn) ⊆ TraceCodes.encoded h d A hn := by
  intro out ho
  have hm := (PlainClosure.machine_bound h.tm σ m).trans hn
  have hnpos : 0 < A.structureValue.size := by have := MachineConstants.enough h.tm; omega
  obtain ⟨c, _, v, e, ht, x, y, heads, hs, he, hp⟩ :=
    (PushRules.operator_iff h.tm emit A.structureValue hm A.tuple _ out).mp ho
  obtain ⟨fact, hf, hfcode⟩ := hp
  have hv := TraceCodes.closure_valid h d A hn fact hf
  cases fact with
  | node r =>
      exact False.elim (ControlValues.value_ne_node (TraceCodes.parameters h.tm d A hn)
        hm c v x heads r hfcode.symm)
  | config t cfg =>
      obtain ⟨hx, rfl, rfl, hh⟩ :=
        (ControlValues.value_eq_configuration (TraceCodes.parameters h.tm d A hn)
          hm c v x heads t cfg hv.2.1).mp hfcode.symm
      have htime : (TupleAddresses.address A.structureValue.size d x).val = t := by
        rw [hx, clock_address, Nat.mod_eq_of_lt hv.1]
      have hytime : (TupleAddresses.address A.structureValue.size d y).val = t + 1 := by omega
      have hnext : t + 1 < A.structureValue.size ^ d := by
        rw [← hytime]
        exact (TupleAddresses.address A.structureValue.size d y).isLt
      have hy : y = clock hnpos (t + 1) := by
        rw [← hytime]
        exact (ControlValues.clock_of_address hnpos y).symm
      refine ⟨PushValues.result e emit t cfg,
        PushValues.result_in_closure (SimulationHorizon.context h A) rfl cfg e emit ht (by omega) hf, ?_⟩
      rw [hx, hy, hh, PushValues.value_code (TraceCodes.parameters h.tm d A hn) hm e emit t cfg] at he
      exact he

/-- Every supported push before the last clock value derives both of its
encoded conclusions from its source configuration alone. -/
theorem derives {t : Nat}
    (cfg : NodeMachine.Cfg h.tm.Γ h.tm.Λ h.tm.σ
      (TimedNodes.Node (InputSegments.Identifier σ m A.structureValue.size)))
    (e : PushEffects.Effect h.tm) (emit : Bool)
    (htarget : PushEffects.target h.tm cfg.cursor cfg.var = some e)
    (hc : cfg.cursor ∈ TM2MicroSupport.controls h.tm)
    (ht : t + 1 < A.structureValue.size ^ d)
    (R : Set (Fin (TraceCodes.arity h.tm σ d) → Fin A.structureValue.size))
    (hp : TraceCodes.code h.tm d A hn (.config t cfg) ∈ R) :
    TraceCodes.code h.tm d A hn (PushValues.result e emit t cfg) ∈
      ParameterizedRules.operator (PushRules.rules h.tm σ m d (TraceCodes.nodeWidth σ d) emit)
        A.structureValue A.tuple R := by
  have hm := (PlainClosure.machine_bound h.tm σ m).trans hn
  have hnpos : 0 < A.structureValue.size := by have := MachineConstants.enough h.tm; omega
  apply (PushRules.operator_iff h.tm emit A.structureValue hm A.tuple R _).mpr
  refine ⟨cfg.cursor, hc, cfg.var, e, htarget, clock hnpos t, clock hnpos (t + 1),
    FactCodes.heads (TraceCodes.parameters h.tm d A hn) cfg.heads, ?_, ?_, hp⟩
  · rw [clock_address, clock_address, Nat.mod_eq_of_lt ht,
      Nat.mod_eq_of_lt (by omega : t < A.structureValue.size ^ d)]
  · exact PushValues.value_code (TraceCodes.parameters h.tm d A hn) hm e emit t cfg

end Lax979537Proofs.PushClosure
