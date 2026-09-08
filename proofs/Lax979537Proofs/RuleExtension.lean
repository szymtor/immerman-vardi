import Lax979537Proofs.RuleConstants

namespace Lax979537Proofs.RuleExtension

open RuleConstants

/-- Add data variables after an existing rule's data block while retaining
the numeral constants at the start. -/
def embed (C v p : Nat) : Fin (C + v) → Fin (C + (v + p)) :=
  Fin.addCases (Fin.castAdd (v + p)) (Fin.natAdd C ∘ Fin.castAdd p)

theorem assignment_embed {C v p n : Nat} (hn : C ≤ n) (a : Fin (v + p) → Fin n) :
    assignment hn a ∘ embed C v p = assignment hn (a ∘ Fin.castAdd p) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [embed, assignment]

end Lax979537Proofs.RuleExtension
