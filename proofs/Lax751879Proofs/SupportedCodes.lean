import Lax751879Proofs.TupleCoding
import Mathlib.Data.Finset.Card

namespace Lax751879Proofs.SupportedCodes

open TupleCoding

variable {α : Type} (S : Finset α)

open scoped Classical in
noncomputable def tag (a : α) : Nat :=
  if h : a ∈ S then finiteTag (⟨a, h⟩ : ↥S) + 1 else 0

theorem tag_of_mem {a : α} (ha : a ∈ S) : tag S a = finiteTag (⟨a, ha⟩ : ↥S) + 1 := by
  classical
  simp [tag, ha]

theorem tag_bound (a : α) : tag S a < S.card + 1 := by
  classical
  by_cases ha : a ∈ S
  · rw [tag_of_mem S ha]
    have h := finiteTag_lt (⟨a, ha⟩ : ↥S)
    simpa using Nat.succ_lt_succ h
  · simp [tag, ha]

theorem tag_injective {a b : α} (ha : a ∈ S) (hb : b ∈ S) (he : tag S a = tag S b) : a = b := by
  rw [tag_of_mem S ha, tag_of_mem S hb] at he
  have hs := finiteTag_injective (Nat.add_right_cancel he)
  exact congrArg Subtype.val hs

/-- A total code on a possibly infinite type. Zero marks unsupported values;
the code is injective on the proved finite support set. -/
noncomputable def code {n : Nat} (hn : S.card + 1 ≤ n) (a : α) : Fin n :=
  ⟨tag S a, (tag_bound S a).trans_le hn⟩

theorem code_injective {n : Nat} (hn : S.card + 1 ≤ n)
    {a b : α} (ha : a ∈ S) (hb : b ∈ S) (he : code S hn a = code S hn b) : a = b :=
  tag_injective S ha hb (congrArg (fun x : Fin n => x.val) he)

/-- A supported symbol cannot collide with an unsupported constant. This is
needed when the distinguished accepting output symbol is never produced. -/
theorem code_eq_iff {n : Nat} (hn : S.card + 1 ≤ n) {a b : α} (ha : a ∈ S) :
    code S hn a = code S hn b ↔ a = b := by
  classical
  constructor
  · intro he
    by_cases hb : b ∈ S
    · exact code_injective S hn ha hb he
    · have ht := congrArg (fun x : Fin n => x.val) he
      change tag S a = tag S b at ht
      rw [tag_of_mem S ha] at ht
      simp [tag, hb] at ht
  · rintro rfl; rfl

end Lax751879Proofs.SupportedCodes
