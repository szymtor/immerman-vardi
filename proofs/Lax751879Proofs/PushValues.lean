import Lax751879Proofs.PushPatterns

namespace Lax751879Proofs.PushValues

open Turing TupleCoding

variable {tm : FinTM2} {Initial : Type} {n iWidth d w : Nat}

def result (e : PushEffects.Effect tm) (emit : Bool) (t : Nat)
    (cfg : NodeMachine.Cfg tm.Γ tm.Λ tm.σ (TimedNodes.Node Initial)) :
    NodeClosure.Fact tm.Γ tm.Λ tm.σ Initial :=
  if emit then .node (.inr t, Sigma.mk e.key e.symbol, cfg.heads e.key)
  else .config (t + 1) ⟨e.next, cfg.var, Function.update cfg.heads e.key (some (.inr t))⟩

theorem value_code (P : FactCodes.Parameters tm Initial n iWidth d w)
    (hn : MachineConstants.bound tm ≤ n) (e : PushEffects.Effect tm) (emit : Bool) (t : Nat)
    (cfg : NodeMachine.Cfg tm.Γ tm.Λ tm.σ (TimedNodes.Node Initial)) :
    PushPatterns.value hn e cfg.var emit
      (clock (d := d) (by have := P.enough; omega) t)
      (clock (d := d) (by have := P.enough; omega) (t + 1)) (FactCodes.heads P cfg.heads) =
      FactCodes.code P (result e emit t cfg) := by
  cases emit with
  | false =>
      dsimp only [PushPatterns.value, PushPatterns.output, Bool.false_eq_true, ↓reduceIte, result]
      rw [HeadPatterns.fresh_code P t, HeadPatterns.update_heads P cfg.heads e.key (some (.inr t))]
      rfl
  | true =>
      dsimp only [PushPatterns.value, PushPatterns.output, ↓reduceIte, result]
      rw [HeadPatterns.fresh_code P t, HeadPatterns.get_heads P cfg.heads e.key]
      rfl

/-- Each of the two push conclusions is a consequence of the semantic
positive closure, using the actual push constructor and emitted record. -/
theorem result_in_closure (C : NodeTrace.Context tm.Γ tm.Λ tm.σ Initial)
    (hprogram : C.program = tm.m) {T t : Nat}
    (cfg : NodeMachine.Cfg tm.Γ tm.Λ tm.σ (TimedNodes.Node Initial))
    (e : PushEffects.Effect tm) (emit : Bool)
    (htarget : PushEffects.target tm cfg.cursor cfg.var = some e)
    (ht : t < T) (hc : NodeClosure.Fact.config t cfg ∈ NodeClosure.closure C T) :
    result e emit t cfg ∈ NodeClosure.closure C T := by
  cases emit with
  | false =>
      rw [← NodeClosure.closure_fixed]
      refine Or.inr ⟨t, cfg, insert (.inr t, Sigma.mk e.key e.symbol, cfg.heads e.key)
        (NodeClosure.nodes (NodeClosure.closure C T)), ht, rfl, hc, ?_⟩
      rw [hprogram]
      have hs := PushEffects.target_step tm (.inr t) (NodeClosure.nodes (NodeClosure.closure C T)) cfg.heads htarget
      cases cfg
      exact hs
  | true =>
      rw [← NodeClosure.closure_fixed]
      refine Or.inr ⟨t, cfg, ht, hc, ?_⟩
      have ha := PushEffects.target_added tm (.inr t) cfg.heads htarget
      cases cfg
      exact ha

end Lax751879Proofs.PushValues
