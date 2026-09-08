import Lax979537Proofs.NodeInput

namespace Lax979537Proofs.RenameRecords

open NodeInput

variable {α β Symbol : Type}

def entries (e : α → β) (xs : List (α × Symbol)) : List (β × Symbol) :=
  xs.map (fun p => (e p.1, p.2))

theorem head_entries (e : α → β) (xs : List (α × Symbol)) :
    head (entries e xs) = (head xs).map e := by
  simp [head, entries, Option.map_map, Function.comp_def]

/-- Renaming nodes maps both the record key and its optional parent. -/
theorem records_entries (e : α → β) (xs : List (α × Symbol))
    (n : β) (a : Symbol) (parent : Option β) :
    (n, a, parent) ∈ records (entries e xs) ↔
      ∃ p parent₀, e p = n ∧ parent₀.map e = parent ∧ (p, a, parent₀) ∈ records xs := by
  induction xs with
  | nil => simp [entries, records]
  | cons x xs ih =>
      rcases x with ⟨q, b⟩
      change (n, a, parent) ∈ insert (e q, b, head (entries e xs)) (records (entries e xs)) ↔ _
      rw [Set.mem_insert_iff, ih, head_entries]
      constructor
      · rintro (he | ⟨p, p₀, hn, hp, hr⟩)
        · cases he
          exact ⟨q, head xs, rfl, rfl, Set.mem_insert _ _⟩
        · exact ⟨p, p₀, hn, hp, Set.mem_insert_of_mem _ hr⟩
      · rintro ⟨p, p₀, rfl, rfl, hr⟩
        rcases Set.mem_insert_iff.mp hr with he | hr
        · cases he; exact Or.inl rfl
        · exact Or.inr ⟨p, p₀, rfl, rfl, hr⟩

end Lax979537Proofs.RenameRecords
