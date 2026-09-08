import Lax979537Proofs.HeadPatterns
import Lax979537Proofs.ReadEffects

namespace Lax979537Proofs.ReadPatterns

open Turing FactPatterns HeadPatterns

variable {tm : FinTM2} {n N d w : Nat}

noncomputable def nextHeads (tm : FinTM2) (key : tm.K) (pop : Bool)
    (h : Fin (ControlRules.headWidth tm w) → Fin N) (parent : Fin (w + 1) → Fin N) :
    Fin (ControlRules.headWidth tm w) → Fin N :=
  if pop then HeadPatterns.update tm h key parent else h

theorem map_nextHeads (tm : FinTM2) (f : Fin N → Fin n) (key : tm.K) (pop : Bool)
    (h : Fin (ControlRules.headWidth tm w) → Fin N) (parent : Fin (w + 1) → Fin N) :
    f ∘ nextHeads tm key pop h parent = nextHeads tm key pop (f ∘ h) (f ∘ parent) := by
  cases pop <;> simp only [nextHeads, Bool.false_eq_true, ↓reduceIte, map_update]

noncomputable def output (tm : FinTM2) (zero control state : Fin N) (key : tm.K) (pop : Bool)
    (time : Fin d → Fin N) (h : Fin (ControlRules.headWidth tm w) → Fin N)
    (parent : Fin (w + 1) → Fin N) : Fin (FactCodes.payloadWidth tm d w + 1) → Fin N :=
  configuration tm zero zero time control state (nextHeads tm key pop h parent)

theorem map_output (tm : FinTM2) (f : Fin N → Fin n) (zero control state : Fin N) (key : tm.K) (pop : Bool)
    (time : Fin d → Fin N) (h : Fin (ControlRules.headWidth tm w) → Fin N) (parent : Fin (w + 1) → Fin N) :
    f ∘ output tm zero control state key pop time h parent =
      output tm (f zero) (f control) (f state) key pop (f ∘ time) (f ∘ h) (f ∘ parent) := by
  simp only [output, map_configuration, map_nextHeads]

noncomputable def value (hn : MachineConstants.bound tm ≤ n) (e : ReadEffects.Effect tm)
    (a : tm.Γ e.key) (time : Fin d → Fin n) (h : Fin (ControlRules.headWidth tm w) → Fin n)
    (parent : Fin (w + 1) → Fin n) : Fin (FactCodes.payloadWidth tm d w + 1) → Fin n :=
  output tm ⟨0, by have := MachineConstants.enough tm; omega⟩
    (SupportedCodes.code _ ((MachineConstants.controls_bound tm).trans hn) e.next)
    (@TupleCoding.finiteCode tm.σ tm.σFin n ((MachineConstants.states_bound tm).trans hn) (e.state (some a)))
    e.key e.pop time h parent

noncomputable def nodeValue (hn : MachineConstants.bound tm ≤ n) (symbol : Sigma tm.Γ)
    (key parent : Fin (w + 1) → Fin n) : Fin (FactCodes.payloadWidth tm d w + 1) → Fin n :=
  record tm d ⟨0, by have := MachineConstants.enough tm; omega⟩
    ⟨1, by have := MachineConstants.enough tm; omega⟩ key
    (SupportedCodes.code _ ((MachineConstants.symbols_bound tm).trans hn) symbol) parent

theorem nextHeads_code {Initial : Type} {iWidth : Nat}
    (P : FactCodes.Parameters tm Initial n iWidth d w) (e : ReadEffects.Effect tm)
    (heads : tm.K → Option (TimedNodes.Node Initial)) (parent : Option (TimedNodes.Node Initial)) :
    nextHeads tm e.key e.pop (FactCodes.heads P heads) (NodeCodes.code (d := d) P.enough P.initial parent) =
      FactCodes.heads P (ReadEffects.nextHeads e heads parent) := by
  unfold nextHeads ReadEffects.nextHeads
  split
  · exact update_heads P heads e.key parent
  · rfl

theorem value_code {Initial : Type} {iWidth : Nat}
    (P : FactCodes.Parameters tm Initial n iWidth d w) (hn : MachineConstants.bound tm ≤ n)
    (e : ReadEffects.Effect tm) (a : tm.Γ e.key) (t : Nat)
    (heads : tm.K → Option (TimedNodes.Node Initial)) (parent : Option (TimedNodes.Node Initial)) :
    value hn e a (TupleCoding.clock (by have := P.enough; omega) t) (FactCodes.heads P heads)
      (NodeCodes.code (d := d) P.enough P.initial parent) =
      FactCodes.code P (.config t ⟨e.next, e.state (some a), ReadEffects.nextHeads e heads parent⟩) := by
  unfold value output
  rw [nextHeads_code P e heads parent]
  rfl

end Lax979537Proofs.ReadPatterns
