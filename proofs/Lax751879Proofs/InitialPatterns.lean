import Lax751879Proofs.HeadPatterns
import Lax751879Proofs.EmptyHead

namespace Lax751879Proofs.InitialPatterns

open Turing TupleCoding FactPatterns HeadPatterns

variable {tm : FinTM2} {n N iWidth d w : Nat}

def parent (zero one : Fin N) (terminal : Bool) (y : Fin iWidth → Fin N) : Fin (w + 1) → Fin N :=
  if terminal then fun _ => zero else fresh zero one y

theorem map_parent (f : Fin N → Fin n) (zero one : Fin N) (terminal : Bool) (y : Fin iWidth → Fin N) :
    f ∘ parent (w := w) zero one terminal y = parent (f zero) (f one) terminal (f ∘ y) := by
  cases terminal <;> simp only [parent, Bool.false_eq_true, ↓reduceIte, map_fresh]
  rfl

def node (tm : FinTM2) (d : Nat) (zero one symbol : Fin N) (terminal : Bool)
    (x y : Fin iWidth → Fin N) : Fin (FactCodes.payloadWidth tm d w + 1) → Fin N :=
  record tm d zero one (fresh zero one x) symbol (parent zero one terminal y)

theorem map_node (tm : FinTM2) (d : Nat) (f : Fin N → Fin n) (zero one symbol : Fin N) (terminal : Bool)
    (x y : Fin iWidth → Fin N) :
    f ∘ node (w := w) tm d zero one symbol terminal x y =
      node tm d (f zero) (f one) (f symbol) terminal (f ∘ x) (f ∘ y) := by
  simp only [node, map_record, map_fresh, map_parent]

noncomputable def configuration (tm : FinTM2) (zero one control state : Fin N)
    (time : Fin d → Fin N) (x : Fin iWidth → Fin N) : Fin (FactCodes.payloadWidth tm d w + 1) → Fin N :=
  FactPatterns.configuration tm zero zero time control state
    (HeadPatterns.update tm (fun _ => zero) tm.k₀ (fresh zero one x))

theorem map_configuration (tm : FinTM2) (f : Fin N → Fin n) (zero one control state : Fin N)
    (time : Fin d → Fin N) (x : Fin iWidth → Fin N) :
    f ∘ configuration (w := w) tm zero one control state time x =
      configuration tm (f zero) (f one) (f control) (f state) (f ∘ time) (f ∘ x) := by
  simp only [configuration, FactPatterns.map_configuration, map_update, map_fresh]
  rfl

theorem initial_code {Initial : Type} (P : FactCodes.Parameters tm Initial n iWidth d w) (p : Initial) :
    fresh (w := w) ⟨0, by have := P.enough; omega⟩ ⟨1, by have := P.enough; omega⟩ (P.initial p) =
      NodeCodes.code (d := d) P.enough P.initial (some (.inl p)) := rfl

theorem heads_none {Initial : Type} (P : FactCodes.Parameters tm Initial n iWidth d w) :
    FactCodes.heads P (fun _ => none) = fun _ => (⟨0, by have := P.enough; omega⟩ : Fin n) := by
  funext i
  simp only [FactCodes.heads, rows, EmptyHead.code_none]

end Lax751879Proofs.InitialPatterns
