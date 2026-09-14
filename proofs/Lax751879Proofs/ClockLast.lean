import Lax751879Proofs.AddressFormulas

namespace Lax751879Proofs.ClockLast

open Lax751879.OrderedStructures Lax751879.FixedPointSyntax Lax751879.FixedPointSemantics
open FormulaMacros TupleOrder TupleAddresses

def formula {σ : Vocabulary} {v d : Nat} {ρ : List Nat} (x : Fin d → Fin v) : RawFormula σ v ρ :=
  .neg (existsBlock d (lexFormula (Fin.natAdd d ∘ x) (Fin.castAdd v)))

theorem firstOrder {σ : Vocabulary} {v d : Nat} {ρ : List Nat} (x : Fin d → Fin v) :
    FirstOrder (formula (σ := σ) (ρ := ρ) x) :=
  (firstOrder_existsBlock _ _).mpr (firstOrder_lex _ _)

theorem no_larger {N : Nat} (x : Fin N) : (¬∃ y : Fin N, x < y) ↔ x.val + 1 = N := by
  constructor
  · intro h
    by_contra he
    have hy : x.val + 1 < N := by have := x.isLt; omega
    exact h ⟨⟨x.val + 1, hy⟩, by change x.val < x.val + 1; omega⟩
  · rintro he ⟨y, hy⟩
    change x.val < y.val at hy
    have := y.isLt
    omega

theorem eval_formula {σ : Vocabulary} {v d : Nat} {ρ : List Nat} (x : Fin d → Fin v)
    (A : OrderedStructure σ) (a : Fin v → Fin A.size) (η : RelationEnv A.size ρ) :
    eval (formula x) A a η ↔ (address A.size d (a ∘ x)).val + 1 = A.size ^ d := by
  simp only [formula, eval, eval_existsBlock, eval_lex_address]
  have hl (b : Fin d → Fin A.size) : Fin.append b a ∘ (Fin.natAdd d ∘ x) = a ∘ x := by
    funext i; simp
  have hr (b : Fin d → Fin A.size) : Fin.append b a ∘ Fin.castAdd v = b := by
    funext i; simp
  simp only [hl, hr]
  rw [← no_larger]
  apply not_congr
  constructor
  · rintro ⟨b, hb⟩; exact ⟨address A.size d b, hb⟩
  · rintro ⟨t, ht⟩; exact ⟨(address A.size d).symm t, by simpa using ht⟩

end Lax751879Proofs.ClockLast
