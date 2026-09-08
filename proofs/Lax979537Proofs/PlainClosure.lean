import Lax979537Proofs.PlainControl
import Lax979537Proofs.ControlValues
import Lax979537Proofs.TraceCodes

namespace Lax979537Proofs.PlainClosure

open Turing Lax979537.OrderedStructures
open NodeClosure TupleCoding

theorem machine_bound (tm : FinTM2) (σ : Vocabulary) (m : Nat) :
    MachineConstants.bound tm ≤ TraceCodes.threshold tm σ m := by
  unfold MachineConstants.bound TraceCodes.threshold
  omega

variable {f : List Bool → Bool} (h : TM2ComputableInPolyTime id (fun b : Bool => [b]) f)
    {σ : Vocabulary} {m : Nat} (d : Nat) (A : PointedStructure σ m)
    (hn : TraceCodes.threshold h.tm σ m ≤ A.structureValue.size)

/-- Every concrete stack-preserving rule is sound for the encoded bounded
trace of the original polynomial-time machine witness. -/
theorem preserves :
    ParameterizedRules.operator (PlainControl.rules h.tm σ m d (TraceCodes.nodeWidth σ d))
      A.structureValue A.tuple (TraceCodes.encoded h d A hn) ⊆ TraceCodes.encoded h d A hn := by
  intro out ho
  have hm := (machine_bound h.tm σ m).trans hn
  have hnpos : 0 < A.structureValue.size := by
    have := MachineConstants.enough h.tm
    omega
  obtain ⟨c, _, v, c', v', ht, x, y, heads, hs, he, hp⟩ :=
    (PlainControl.operator_iff h.tm A.structureValue hm A.tuple _ out).mp ho
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
      refine ⟨.config (t + 1) ⟨c', v', cfg.heads⟩, ?_, ?_⟩
      · rw [← closure_fixed]
        refine Or.inr ⟨t, cfg, nodes (closure (SimulationHorizon.context h A)
          (A.structureValue.size ^ d - 1)), by omega, rfl, hf, ?_⟩
        have hstep := PlainControl.target_step h.tm (.inr t)
          (nodes (closure (SimulationHorizon.context h A) (A.structureValue.size ^ d - 1))) cfg.heads ht
        cases cfg
        exact hstep
      · rw [hy, hh] at he
        exact he

/-- Conversely, each supported stack-preserving step before the final
clock value has a witness for one of the concrete finite rules. -/
theorem derives {t : Nat}
    (cfg : NodeMachine.Cfg h.tm.Γ h.tm.Λ h.tm.σ
      (TimedNodes.Node (InputSegments.Identifier σ m A.structureValue.size)))
    (c' : TM2Micro.Cursor h.tm.Γ h.tm.Λ h.tm.σ) (v' : h.tm.σ)
    (htarget : PlainControl.target h.tm cfg.cursor cfg.var = some (c', v'))
    (hc : cfg.cursor ∈ TM2MicroSupport.controls h.tm)
    (ht : t + 1 < A.structureValue.size ^ d)
    (R : Set (Fin (TraceCodes.arity h.tm σ d) → Fin A.structureValue.size))
    (hp : TraceCodes.code h.tm d A hn (.config t cfg) ∈ R) :
    TraceCodes.code h.tm d A hn (.config (t + 1) ⟨c', v', cfg.heads⟩) ∈
      ParameterizedRules.operator (PlainControl.rules h.tm σ m d (TraceCodes.nodeWidth σ d))
        A.structureValue A.tuple R := by
  have hm := (machine_bound h.tm σ m).trans hn
  have hnpos : 0 < A.structureValue.size := by have := MachineConstants.enough h.tm; omega
  apply (PlainControl.operator_iff h.tm A.structureValue hm A.tuple R _).mpr
  refine ⟨cfg.cursor, hc, cfg.var, c', v', htarget,
    clock hnpos t, clock hnpos (t + 1),
    FactCodes.heads (TraceCodes.parameters h.tm d A hn) cfg.heads, ?_, rfl, hp⟩
  rw [clock_address, clock_address, Nat.mod_eq_of_lt ht,
    Nat.mod_eq_of_lt (by omega : t < A.structureValue.size ^ d)]

end Lax979537Proofs.PlainClosure
