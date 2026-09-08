import Lax979537Proofs.EmptyReadRules
import Lax979537Proofs.PlainClosure

namespace Lax979537Proofs.EmptyReadClosure

open Turing Lax979537.OrderedStructures
open NodeClosure TupleCoding

variable {f : List Bool → Bool} (h : TM2ComputableInPolyTime id (fun b : Bool => [b]) f)
    {σ : Vocabulary} {m : Nat} (d : Nat) (A : PointedStructure σ m)
    (hn : TraceCodes.threshold h.tm σ m ≤ A.structureValue.size)

/-- An all-zero head guard denotes the actual empty stack head. Thus both
empty-pop and empty-peek rules preserve the encoded canonical trace. -/
theorem preserves :
    ParameterizedRules.operator (EmptyReadRules.rules h.tm σ m d (TraceCodes.nodeWidth σ d))
      A.structureValue A.tuple (TraceCodes.encoded h d A hn) ⊆ TraceCodes.encoded h d A hn := by
  intro out ho
  have hm := (PlainClosure.machine_bound h.tm σ m).trans hn
  have hnpos : 0 < A.structureValue.size := by have := MachineConstants.enough h.tm; omega
  obtain ⟨c, _, v, e, ht, x, y, heads, hs, hz, he, hp⟩ :=
    (EmptyReadRules.operator_iff h.tm A.structureValue hm A.tuple _ out).mp ho
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
      rw [hh, HeadPatterns.get_heads] at hz
      have hempty : cfg.heads e.key = none := by
        let P := TraceCodes.parameters h.tm d A hn
        apply NodeCodes.code_injective P.enough P.initial P.initial_injective P.initial_width P.clock_width
          (hv.2.2 e.key) (by intro n he; cases he)
        rw [EmptyHead.code_none]
        exact hz
      have htime : (TupleAddresses.address A.structureValue.size d x).val = t := by
        rw [hx, clock_address, Nat.mod_eq_of_lt hv.1]
      have hytime : (TupleAddresses.address A.structureValue.size d y).val = t + 1 := by omega
      have hnext : t + 1 < A.structureValue.size ^ d := by
        rw [← hytime]
        exact (TupleAddresses.address A.structureValue.size d y).isLt
      have hy : y = clock hnpos (t + 1) := by
        rw [← hytime]
        exact (ControlValues.clock_of_address hnpos y).symm
      refine ⟨.config (t + 1) ⟨e.next, e.state none, cfg.heads⟩, ?_, ?_⟩
      · rw [← closure_fixed]
        refine Or.inr ⟨t, cfg, nodes (closure (SimulationHorizon.context h A)
          (A.structureValue.size ^ d - 1)), by omega, rfl, hf, ?_⟩
        have hstep := ReadEffects.empty_step h.tm (.inr t)
          (nodes (closure (SimulationHorizon.context h A) (A.structureValue.size ^ d - 1))) cfg.heads ht hempty
        cases cfg
        exact hstep
      · rw [hy, hh] at he
        exact he

theorem derives {t : Nat}
    (cfg : NodeMachine.Cfg h.tm.Γ h.tm.Λ h.tm.σ
      (TimedNodes.Node (InputSegments.Identifier σ m A.structureValue.size)))
    (e : ReadEffects.Effect h.tm)
    (htarget : ReadEffects.target h.tm cfg.cursor cfg.var = some e)
    (hempty : cfg.heads e.key = none)
    (hc : cfg.cursor ∈ TM2MicroSupport.controls h.tm)
    (ht : t + 1 < A.structureValue.size ^ d)
    (R : Set (Fin (TraceCodes.arity h.tm σ d) → Fin A.structureValue.size))
    (hp : TraceCodes.code h.tm d A hn (.config t cfg) ∈ R) :
    TraceCodes.code h.tm d A hn (.config (t + 1) ⟨e.next, e.state none, cfg.heads⟩) ∈
      ParameterizedRules.operator (EmptyReadRules.rules h.tm σ m d (TraceCodes.nodeWidth σ d))
        A.structureValue A.tuple R := by
  have hm := (PlainClosure.machine_bound h.tm σ m).trans hn
  have hnpos : 0 < A.structureValue.size := by have := MachineConstants.enough h.tm; omega
  apply (EmptyReadRules.operator_iff h.tm A.structureValue hm A.tuple R _).mpr
  refine ⟨cfg.cursor, hc, cfg.var, e, htarget, clock hnpos t, clock hnpos (t + 1),
    FactCodes.heads (TraceCodes.parameters h.tm d A hn) cfg.heads, ?_, ?_, rfl, hp⟩
  · rw [clock_address, clock_address, Nat.mod_eq_of_lt ht,
      Nat.mod_eq_of_lt (by omega : t < A.structureValue.size ^ d)]
  · rw [HeadPatterns.get_heads, hempty, EmptyHead.code_none]

end Lax979537Proofs.EmptyReadClosure
