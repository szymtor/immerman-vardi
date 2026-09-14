import Lax751879Proofs.ControlRules

namespace Lax751879Proofs.ControlValues

open Turing TupleCoding FactPatterns

variable {tm : FinTM2} {Initial : Type} {n iWidth d w : Nat}
  (P : FactCodes.Parameters tm Initial n iWidth d w)
  (hn : MachineConstants.bound tm ≤ n)

theorem value_eq_configuration
    (c : TM2Micro.Cursor tm.Γ tm.Λ tm.σ) (v : tm.σ)
    (x : Fin d → Fin n) (h : Fin (ControlRules.headWidth tm w) → Fin n)
    (t : Nat) (cfg : NodeMachine.Cfg tm.Γ tm.Λ tm.σ (TimedNodes.Node Initial))
    (hc : cfg.cursor ∈ TM2MicroSupport.controls tm) :
    ControlRules.value hn c v x h = FactCodes.code P (.config t cfg) ↔
      x = clock (by have := P.enough; omega) t ∧ c = cfg.cursor ∧ v = cfg.var ∧
        h = FactCodes.heads P cfg.heads := by
  constructor
  · intro he
    dsimp only [ControlRules.value, configuration, FactCodes.code, FactCodes.configuration] at he
    have hp := (Fin.cons_inj.mp he).2
    have hu := pad_injective _ (Nat.le_max_left (FactCodes.configWidth tm d w) (FactCodes.recordWidth w)) hp
    obtain ⟨hx, hr⟩ := append_inj hu
    obtain ⟨hcur, hr⟩ := Fin.cons_inj.mp hr
    obtain ⟨hv, hh⟩ := Fin.cons_inj.mp hr
    have hcursor : c = cfg.cursor := by
      apply Eq.symm
      apply (SupportedCodes.code_eq_iff _ P.controls_bound hc).mp
      exact hcur.symm
    have hstate : v = cfg.var := @finiteCode_injective tm.σ tm.σFin n P.states_bound _ _ hv
    exact ⟨hx, hcursor, hstate, hh⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    rfl

theorem value_ne_node
    (c : TM2Micro.Cursor tm.Γ tm.Λ tm.σ) (v : tm.σ)
    (x : Fin d → Fin n) (h : Fin (ControlRules.headWidth tm w) → Fin n)
    (r : TimedNodes.Node Initial × Sigma tm.Γ × Option (TimedNodes.Node Initial)) :
    ControlRules.value hn c v x h ≠ FactCodes.code P (.node r) := by
  intro he
  have ht : (0 : Nat) = 1 := congrArg (fun a : Fin n => a.val) (congrFun he 0)
  cases ht

theorem clock_of_address (hn : 0 < n) (x : Fin d → Fin n) :
    clock hn (TupleAddresses.address n d x).val = x := by
  unfold clock
  have he : (⟨(TupleAddresses.address n d x).val % n ^ d,
      Nat.mod_lt _ (Nat.pow_pos hn)⟩ : Fin (n ^ d)) = TupleAddresses.address n d x :=
    Fin.ext (Nat.mod_eq_of_lt (TupleAddresses.address n d x).isLt)
  rw [he]
  exact (TupleAddresses.address n d).symm_apply_apply x

end Lax751879Proofs.ControlValues
