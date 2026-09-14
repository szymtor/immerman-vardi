import Lax751879Proofs.ReadPatterns

namespace Lax751879Proofs.ReadRecordValues

open Turing TupleCoding FactPatterns

variable {tm : FinTM2} {Initial : Type} {n iWidth d w : Nat}
    (P : FactCodes.Parameters tm Initial n iWidth d w) (hn : MachineConstants.bound tm ≤ n)

theorem node_eq (symbol : Sigma tm.Γ) (key parent : Fin (w + 1) → Fin n)
    (r : TimedNodes.Node Initial × Sigma tm.Γ × Option (TimedNodes.Node Initial))
    (ha : r.2.1 ∈ TM2Alphabet.alphabet tm) :
    ReadPatterns.nodeValue (d := d) hn symbol key parent = FactCodes.code P (.node r) ↔
      key = NodeCodes.code (d := d) P.enough P.initial (some r.1) ∧ symbol = r.2.1 ∧
        parent = NodeCodes.code (d := d) P.enough P.initial r.2.2 := by
  constructor
  · intro he
    dsimp only [ReadPatterns.nodeValue, record, FactCodes.code, FactCodes.record] at he
    have hp := (Fin.cons_inj.mp he).2
    have hu := pad_injective _ (Nat.le_max_right (FactCodes.configWidth tm d w) (FactCodes.recordWidth w)) hp
    obtain ⟨hk, hr⟩ := append_inj hu
    obtain ⟨hs, hparent⟩ := Fin.cons_inj.mp hr
    have hsymbol : symbol = r.2.1 := ((SupportedCodes.code_eq_iff _ P.symbols_bound ha).mp hs.symm).symm
    exact ⟨hk, hsymbol, hparent⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

theorem node_ne_configuration (symbol : Sigma tm.Γ) (key parent : Fin (w + 1) → Fin n)
    (t : Nat) (cfg : NodeMachine.Cfg tm.Γ tm.Λ tm.σ (TimedNodes.Node Initial)) :
    ReadPatterns.nodeValue (d := d) hn symbol key parent ≠ FactCodes.code P (.config t cfg) := by
  intro he
  have ht : (1 : Nat) = 0 := congrArg (fun a : Fin n => a.val) (congrFun he 0)
  cases ht

end Lax751879Proofs.ReadRecordValues
