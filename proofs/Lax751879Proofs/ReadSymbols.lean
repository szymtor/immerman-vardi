import Lax751879Proofs.TM2Alphabet

namespace Lax751879Proofs.ReadSymbols

open Turing

/-- Only symbols in the proved finite alphabet need a nonempty read rule,
even when the type of an internal stack alphabet is infinite. -/
abbrev Symbol (tm : FinTM2) (k : tm.K) := {a : tm.Γ k // Sigma.mk k a ∈ TM2Alphabet.alphabet tm}

noncomputable instance (tm : FinTM2) (k : tm.K) : Fintype (Symbol tm k) := by
  classical
  exact Fintype.ofInjective
    (fun a : Symbol tm k => (⟨Sigma.mk k a.val, a.property⟩ : ↥(TM2Alphabet.alphabet tm)))
    (by intro a b he; apply Subtype.ext; simpa using congrArg Subtype.val he)

open scoped Classical in
noncomputable def values (tm : FinTM2) (k : tm.K) : List (tm.Γ k) :=
  (Finset.univ : Finset (Symbol tm k)).toList.map Subtype.val

theorem mem_values (tm : FinTM2) (k : tm.K) (a : tm.Γ k) :
    a ∈ values tm k ↔ Sigma.mk k a ∈ TM2Alphabet.alphabet tm := by
  classical
  simp only [values, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨b, rfl⟩; exact b.property
  · intro ha; exact ⟨⟨a, ha⟩, rfl⟩

end Lax751879Proofs.ReadSymbols
