import Lax751879Proofs.FactCodes

namespace Lax751879Proofs.FactPatterns

open Turing TupleCoding

variable {n N k w d : Nat}

theorem map_pad (f : Fin N → Fin n) (zero : Fin N) (x : Fin k → Fin N) :
    f ∘ pad (w := w) zero x = pad (f zero) (f ∘ x) := by
  funext i
  simp only [Function.comp_apply, pad]
  split <;> rfl

theorem map_cons {α β : Type} (f : α → β) (x : α) (xs : Fin k → α) :
    f ∘ Fin.cons x xs = Fin.cons (f x) (f ∘ xs) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem map_append {α β : Type} (f : α → β) (x : Fin k → α) (y : Fin w → α) :
    f ∘ Fin.append x y = Fin.append (f ∘ x) (f ∘ y) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

theorem map_rows {K : Type} {c : Nat} (f : Fin N → Fin n)
    (keys : K ≃ Fin c) (x : K → Fin w → Fin N) :
    f ∘ rows keys x = rows keys (fun k => f ∘ x k) := rfl

/-- The same tuple layout serves as a variable pattern and as a tuple of
domain elements. The tag and padding values are explicit arguments. -/
def configuration (tm : FinTM2) (zero tag : Fin N) (time : Fin d → Fin N)
    (control state : Fin N) (heads : Fin (FactCodes.stackCount tm * (w + 1)) → Fin N) :
    Fin (FactCodes.payloadWidth tm d w + 1) → Fin N :=
  Fin.cons tag (pad zero (Fin.append time (Fin.cons control (Fin.cons state heads))))

def record (tm : FinTM2) (d : Nat) (zero tag : Fin N)
    (key : Fin (w + 1) → Fin N) (symbol : Fin N) (parent : Fin (w + 1) → Fin N) :
    Fin (FactCodes.payloadWidth tm d w + 1) → Fin N :=
  Fin.cons tag (pad zero (Fin.append key (Fin.cons symbol parent)))

theorem map_configuration (tm : FinTM2) (f : Fin N → Fin n) (zero tag : Fin N)
    (time : Fin d → Fin N) (control state : Fin N)
    (heads : Fin (FactCodes.stackCount tm * (w + 1)) → Fin N) :
    f ∘ configuration tm zero tag time control state heads =
      configuration tm (f zero) (f tag) (f ∘ time) (f control) (f state) (f ∘ heads) := by
  simp only [configuration, map_cons, map_pad, map_append]

theorem map_record (tm : FinTM2) (d : Nat) (f : Fin N → Fin n) (zero tag : Fin N)
    (key : Fin (w + 1) → Fin N) (symbol : Fin N) (parent : Fin (w + 1) → Fin N) :
    f ∘ record tm d zero tag key symbol parent =
      record tm d (f zero) (f tag) (f ∘ key) (f symbol) (f ∘ parent) := by
  simp only [record, map_cons, map_pad, map_append]

theorem code_configuration {tm : FinTM2} {Initial : Type} {iWidth : Nat}
    (P : FactCodes.Parameters tm Initial n iWidth d w) (t : Nat)
    (c : NodeMachine.Cfg tm.Γ tm.Λ tm.σ (TimedNodes.Node Initial)) :
    FactCodes.code P (.config t c) = configuration tm
      ⟨0, by have := P.enough; omega⟩ ⟨0, by have := P.enough; omega⟩
      (clock (by have := P.enough; omega) t)
      (SupportedCodes.code _ P.controls_bound c.cursor)
      (@finiteCode tm.σ tm.σFin n P.states_bound c.var) (FactCodes.heads P c.heads) := rfl

theorem code_record {tm : FinTM2} {Initial : Type} {iWidth : Nat}
    (P : FactCodes.Parameters tm Initial n iWidth d w)
    (r : TimedNodes.Node Initial × Sigma tm.Γ × Option (TimedNodes.Node Initial)) :
    FactCodes.code P (.node r) = record tm d
      ⟨0, by have := P.enough; omega⟩ ⟨1, by have := P.enough; omega⟩
      (NodeCodes.code (d := d) P.enough P.initial (some r.1))
      (SupportedCodes.code _ P.symbols_bound r.2.1)
      (NodeCodes.code (d := d) P.enough P.initial r.2.2) := rfl

end Lax751879Proofs.FactPatterns
