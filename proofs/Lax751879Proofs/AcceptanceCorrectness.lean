import Lax751879Proofs.AcceptanceFormula

namespace Lax751879Proofs.AcceptanceCorrectness

open Turing Lax751879.OrderedStructures Lax751879.FixedPointSemantics
open NodeClosure TupleCoding

theorem eval_iff {f : List Bool → Bool} (h : TM2ComputableInPolyTime id (fun b : Bool => [b]) f)
    {σ : Vocabulary} {m : Nat} (d : Nat) (A : PointedStructure σ m)
    (hn : TraceCodes.threshold h.tm σ m ≤ A.structureValue.size) (answer : h.tm.Γ h.tm.k₁) :
    eval (AcceptanceFormula.formula h.tm h.inputAlphabet answer σ m d) A.structureValue A.tuple (fun i => Fin.elim0 i) ↔
      NodeAcceptance.accepts (closure (SimulationHorizon.context h A) (A.structureValue.size ^ d - 1))
        (A.structureValue.size ^ d - 1) h.tm.k₁ answer := by
  rw [AcceptanceFormula.eval_formula h d A hn answer]
  have hm := (PlainClosure.machine_bound h.tm σ m).trans hn
  have hnpos : 0 < A.structureValue.size := by unfold TraceCodes.threshold at hn; omega
  have hpow : 0 < A.structureValue.size ^ d := Nat.pow_pos hnpos
  constructor
  · rintro ⟨state, x, heads, p, hlast, hc, hr⟩
    obtain ⟨fact, hf, hfcode⟩ := hc
    have hv := TraceCodes.closure_valid h d A hn fact hf
    cases fact with
    | node r =>
        exact False.elim (ControlValues.value_ne_node (TraceCodes.parameters h.tm d A hn)
          hm (.boundary none) state x heads r hfcode.symm)
    | config t cfg =>
        obtain ⟨hx, hhalt, _, hh⟩ :=
          (ControlValues.value_eq_configuration (TraceCodes.parameters h.tm d A hn)
            hm (.boundary none) state x heads t cfg hv.2.1).mp hfcode.symm
        have ht : t = A.structureValue.size ^ d - 1 := by
          rw [hx, clock_address, Nat.mod_eq_of_lt hv.1] at hlast
          omega
        subst t
        obtain ⟨recordFact, hrf, hrcode⟩ := hr
        have hrv := TraceCodes.closure_valid h d A hn recordFact hrf
        cases recordFact with
        | config s other =>
            exact False.elim (ReadRecordValues.node_ne_configuration (TraceCodes.parameters h.tm d A hn)
              hm (Sigma.mk h.tm.k₁ answer) (HeadPatterns.get h.tm heads h.tm.k₁) p s other hrcode.symm)
        | node r =>
            rcases r with ⟨key, symbol, parent⟩
            obtain ⟨hk, hsymbol, _⟩ :=
              (ReadRecordValues.node_eq (TraceCodes.parameters h.tm d A hn) hm
                (Sigma.mk h.tm.k₁ answer) (HeadPatterns.get h.tm heads h.tm.k₁) p (key, symbol, parent) hrv.2.1).mp hrcode.symm
            dsimp only at hsymbol hk
            subst symbol
            rw [hh, HeadPatterns.get_heads] at hk
            have hhead : cfg.heads h.tm.k₁ = some key := by
              let P := TraceCodes.parameters h.tm d A hn
              exact NodeCodes.code_injective P.enough P.initial P.initial_injective P.initial_width P.clock_width
                (hv.2.2 h.tm.k₁) (by intro n he; cases he; exact hrv.1) hk
            exact ⟨cfg, parent, hf, hhalt.symm, Or.inr ⟨key, Sigma.mk h.tm.k₁ answer, hhead, rfl, hrf⟩⟩
  · rintro ⟨cfg, parent, hc, hhalt, hr⟩
    obtain ⟨key, hhead, hrecord⟩ :=
      (ReadDerivation.read_some (nodes (closure (SimulationHorizon.context h A) (A.structureValue.size ^ d - 1)))
        (cfg.heads h.tm.k₁) parent (Sigma.mk h.tm.k₁ answer)).mp hr
    let P := TraceCodes.parameters h.tm d A hn
    refine ⟨cfg.var, clock hnpos (A.structureValue.size ^ d - 1), FactCodes.heads P cfg.heads,
      NodeCodes.code (d := d) P.enough P.initial parent, ?_, ?_, ?_⟩
    · rw [clock_address, Nat.mod_eq_of_lt (by omega : A.structureValue.size ^ d - 1 < A.structureValue.size ^ d)]
      omega
    · have he : ControlRules.value hm (.boundary none) cfg.var (clock hnpos (A.structureValue.size ^ d - 1))
          (FactCodes.heads P cfg.heads) = TraceCodes.code h.tm d A hn (.config (A.structureValue.size ^ d - 1) cfg) := by
        rw [← hhalt]
        rfl
      rw [he]
      exact ⟨_, hc, rfl⟩
    · rw [HeadPatterns.get_heads, hhead]
      exact ⟨.node (key, Sigma.mk h.tm.k₁ answer, parent), hrecord, rfl⟩

end Lax751879Proofs.AcceptanceCorrectness
