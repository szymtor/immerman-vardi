import Lax979537Proofs.NonemptyPatterns
import Lax979537Proofs.ClockLast

namespace Lax979537Proofs.AcceptRule

open Turing Lax979537.OrderedStructures RuleConstants NonemptyPatterns

def outputEffect (tm : FinTM2) : ReadEffects.Effect tm :=
  ⟨tm.k₁, fun _ => tm.initialState, .boundary none, false⟩

noncomputable def template (tm : FinTM2) (answer : tm.Γ tm.k₁) (σ : Vocabulary) (m d w : Nat) (state : tm.σ) :
    Template σ m (FactCodes.payloadWidth tm d w + 1) (MachineConstants.bound tm) where
  numVars := numVars tm m d w
  guard := ClockLast.formula (xvars tm m d w)
  guard_firstOrder := ClockLast.firstOrder _
  parameters := qvars tm m d w
  head := source tm m d w (.boundary none) state
  premises := [source tm m d w (.boundary none) state, node tm m d w (outputEffect tm) answer]

theorem holds {tm : FinTM2} (answer : tm.Γ tm.k₁) {σ : Vocabulary} {m d w : Nat} (state : tm.σ)
    (A : OrderedStructure σ) (hn : MachineConstants.bound tm ≤ A.size)
    (q : Fin m → Fin A.size) (R : Set (Fin (FactCodes.payloadWidth tm d w + 1) → Fin A.size)) :
    (∃ out, (compile (template tm answer σ m d w state)).holds A q R out) ↔
      ∃ x : Fin d → Fin A.size, ∃ h : Fin (ControlRules.headWidth tm w) → Fin A.size,
        ∃ p : Fin (w + 1) → Fin A.size,
          (TupleAddresses.address A.size d x).val + 1 = A.size ^ d ∧
          ControlRules.value hn (.boundary none) state x h ∈ R ∧
          ReadPatterns.nodeValue (d := d) hn (Sigma.mk tm.k₁ answer) (HeadPatterns.get tm h tm.k₁) p ∈ R := by
  simp_rw [compile_holds _ A hn]
  dsimp only [RuleConstants.holds, template]
  constructor
  · rintro ⟨out, a, hg, _, _, hp⟩
    refine ⟨a ∘ xvars tm m d w, a ∘ hvars tm m d w, a ∘ pvars tm m d w,
      (ClockLast.eval_formula (ρ := []) _ _ _ _).mp hg, ?_, ?_⟩
    · have hs := hp _ (List.mem_cons_self ..)
      rwa [assignment_source] at hs
    · have hs := hp _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
      rwa [assignment_node] at hs
  · rintro ⟨x, h, p, hx, hc, hr⟩
    refine ⟨ControlRules.value hn (.boundary none) state x h, data q x x h p, ?_, data_q q x x h p, ?_, ?_⟩
    · apply (ClockLast.eval_formula (ρ := []) _ _ _ _).mpr
      simpa only [data_x q x x h p] using hx
    · rw [assignment_source, data_x q x x h p, data_h q x x h p]
    · intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · rw [assignment_source, data_x q x x h p, data_h q x x h p]
        exact hc
      · have hb' : b = node tm m d w (outputEffect tm) answer := List.mem_singleton.mp hb
        subst b
        rw [assignment_node, data_h q x x h p, data_p q x x h p]
        exact hr

end Lax979537Proofs.AcceptRule
