import Lax751879Proofs.NonemptyReadRules
import Lax751879Proofs.ReadRecordValues
import Lax751879Proofs.PlainClosure

namespace Lax751879Proofs.NonemptyReadClosure

open Turing Lax751879.OrderedStructures
open NodeClosure TupleCoding

variable {f : List Bool → Bool} (h : TM2ComputableInPolyTime id (fun b : Bool => [b]) f)
    {σ : Vocabulary} {m : Nat} (d : Nat) (A : PointedStructure σ m)
    (hn : TraceCodes.threshold h.tm σ m ≤ A.structureValue.size)

/-- A positive node premise identifies the actual source head, its typed
symbol, and its parent. Both nonempty read operations therefore preserve
the encoded canonical trace. -/
theorem preserves :
    ParameterizedRules.operator (NonemptyReadRules.rules h.tm σ m d (TraceCodes.nodeWidth σ d))
      A.structureValue A.tuple (TraceCodes.encoded h d A hn) ⊆ TraceCodes.encoded h d A hn := by
  intro out ho
  have hm := (PlainClosure.machine_bound h.tm σ m).trans hn
  have hnpos : 0 < A.structureValue.size := by have := MachineConstants.enough h.tm; omega
  obtain ⟨c, _, v, e, htarget, a, _, x, y, heads, p, hs, he, hc, hr⟩ :=
    (NonemptyReadRules.operator_iff h.tm A.structureValue hm A.tuple _ out).mp ho
  obtain ⟨fact, hf, hfcode⟩ := hc
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
      obtain ⟨recordFact, hrf, hrcode⟩ := hr
      have hrv := TraceCodes.closure_valid h d A hn recordFact hrf
      cases recordFact with
      | config s other =>
          exact False.elim (ReadRecordValues.node_ne_configuration (TraceCodes.parameters h.tm d A hn)
            hm (Sigma.mk e.key a) (HeadPatterns.get h.tm heads e.key) p s other hrcode.symm)
      | node r =>
          rcases r with ⟨key, symbol, parent⟩
          obtain ⟨hk, hsymbol, hparent⟩ :=
            (ReadRecordValues.node_eq (TraceCodes.parameters h.tm d A hn) hm
              (Sigma.mk e.key a) (HeadPatterns.get h.tm heads e.key) p (key, symbol, parent) hrv.2.1).mp hrcode.symm
          dsimp only at hsymbol hparent hk
          subst symbol
          rw [hh, HeadPatterns.get_heads] at hk
          have hhead : cfg.heads e.key = some key := by
            let P := TraceCodes.parameters h.tm d A hn
            exact NodeCodes.code_injective P.enough P.initial P.initial_injective P.initial_width P.clock_width
              (hv.2.2 e.key) (by intro n he; cases he; exact hrv.1) hk
          refine ⟨.config (t + 1) ⟨e.next, e.state (some a), ReadEffects.nextHeads e cfg.heads parent⟩, ?_, ?_⟩
          · rw [← closure_fixed]
            refine Or.inr ⟨t, cfg, nodes (closure (SimulationHorizon.context h A)
              (A.structureValue.size ^ d - 1)), by omega, rfl, hf, ?_⟩
            have hread : PersistentStack.Read (nodes (closure (SimulationHorizon.context h A)
                (A.structureValue.size ^ d - 1))) (cfg.heads e.key) (some (Sigma.mk e.key a)) parent :=
              Or.inr ⟨key, Sigma.mk e.key a, hhead, rfl, hrf⟩
            have hstep := ReadEffects.target_step h.tm (.inr t)
              (nodes (closure (SimulationHorizon.context h A) (A.structureValue.size ^ d - 1)))
              cfg.heads htarget (some a) parent hread
            cases cfg
            exact hstep
          · rw [hy, hh, hparent, ReadPatterns.value_code (TraceCodes.parameters h.tm d A hn)
              hm e a (t + 1) cfg.heads parent] at he
            exact he

theorem derives {t : Nat}
    (cfg : NodeMachine.Cfg h.tm.Γ h.tm.Λ h.tm.σ
      (TimedNodes.Node (InputSegments.Identifier σ m A.structureValue.size)))
    (e : ReadEffects.Effect h.tm) (a : h.tm.Γ e.key)
    (key : TimedNodes.Node (InputSegments.Identifier σ m A.structureValue.size))
    (parent : Option (TimedNodes.Node (InputSegments.Identifier σ m A.structureValue.size)))
    (htarget : ReadEffects.target h.tm cfg.cursor cfg.var = some e)
    (hhead : cfg.heads e.key = some key)
    (ha : Sigma.mk e.key a ∈ TM2Alphabet.alphabet h.tm)
    (hc : cfg.cursor ∈ TM2MicroSupport.controls h.tm)
    (ht : t + 1 < A.structureValue.size ^ d)
    (R : Set (Fin (TraceCodes.arity h.tm σ d) → Fin A.structureValue.size))
    (hp : TraceCodes.code h.tm d A hn (.config t cfg) ∈ R)
    (hr : TraceCodes.code h.tm d A hn (.node (key, Sigma.mk e.key a, parent)) ∈ R) :
    TraceCodes.code h.tm d A hn
        (.config (t + 1) ⟨e.next, e.state (some a), ReadEffects.nextHeads e cfg.heads parent⟩) ∈
      ParameterizedRules.operator (NonemptyReadRules.rules h.tm σ m d (TraceCodes.nodeWidth σ d))
        A.structureValue A.tuple R := by
  have hm := (PlainClosure.machine_bound h.tm σ m).trans hn
  have hnpos : 0 < A.structureValue.size := by have := MachineConstants.enough h.tm; omega
  apply (NonemptyReadRules.operator_iff h.tm A.structureValue hm A.tuple R _).mpr
  refine ⟨cfg.cursor, hc, cfg.var, e, htarget, a, ha, clock hnpos t, clock hnpos (t + 1),
    FactCodes.heads (TraceCodes.parameters h.tm d A hn) cfg.heads,
    NodeCodes.code (d := d) (TraceCodes.parameters h.tm d A hn).enough
      (TraceCodes.parameters h.tm d A hn).initial parent, ?_, ?_, hp, ?_⟩
  · rw [clock_address, clock_address, Nat.mod_eq_of_lt ht,
      Nat.mod_eq_of_lt (by omega : t < A.structureValue.size ^ d)]
  · exact ReadPatterns.value_code (TraceCodes.parameters h.tm d A hn) hm e a (t + 1) cfg.heads parent
  · rw [HeadPatterns.get_heads, hhead]
    exact hr

end Lax751879Proofs.NonemptyReadClosure
