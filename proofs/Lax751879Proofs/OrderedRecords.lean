import Lax751879Proofs.SortedLinks

namespace Lax751879Proofs.OrderedRecords

open NodeInput SortedLinks

variable {α β : Type}

theorem head_map (xs : List α) (f : α → β) :
    head (xs.map (fun p => (p, f p))) = xs.head? := by
  simp [head, Option.map_map, Function.comp_def]

theorem records_map_mem (xs : List α) (f : α → β) (p : α) (a : β) (parent : Option α) :
    (p, a, parent) ∈ records (xs.map (fun q => (q, f q))) ↔
      ∃ i : Fin xs.length, xs.get i = p ∧ a = f p ∧ parent = xs[i.val + 1]? := by
  induction xs with
  | nil => simp [records]
  | cons q xs ih =>
      simp only [List.map_cons, records, Set.mem_insert_iff, ih, head_map]
      constructor
      · rintro (he | ⟨i, hi, ha, hp⟩)
        · cases he
          exact ⟨0, rfl, rfl, by simp [List.head?_eq_getElem?]⟩
        · exact ⟨i.succ, by simpa using hi, ha, by simpa using hp⟩
      · rintro ⟨⟨i, hib⟩, hi, ha, hp⟩
        cases i with
        | zero =>
            have hq : q = p := hi
            subst p
            subst a
            left
            simpa [List.head?_eq_getElem?] using hp
        | succ i =>
            right
            exact ⟨⟨i, Nat.lt_of_succ_lt_succ hib⟩, by simpa using hi,
              ha, by simpa [Nat.add_assoc] using hp⟩

def Parent (xs : List α) (r : α → Nat) (p : α) : Option α → Prop
  | none => Last xs r p
  | some q => Next xs r p q

theorem parent_get (xs : List α) (r : α → Nat)
    (hs : xs.Pairwise (fun p q => r p < r q)) (i : Fin xs.length) (parent : Option α) :
    Parent xs r (xs.get i) parent ↔ parent = xs[i.val + 1]? := by
  cases parent with
  | none =>
      rw [Parent, last_get xs r hs]
      rw [eq_comm (a := (none : Option α)), List.getElem?_eq_none_iff]
      have := i.isLt
      omega
  | some q =>
      change Next xs r (xs.get i) q ↔ some q = xs[i.val + 1]?
      constructor
      · intro h
        obtain ⟨j, rfl⟩ := List.get_of_mem h.2.1
        have hij := (next_get xs r hs i j).mp h
        rw [hij, List.getElem?_eq_getElem j.isLt]
        rfl
      · intro h
        obtain ⟨hj, he⟩ := List.getElem?_eq_some_iff.mp h.symm
        have hh := (next_get xs r hs i ⟨i.val + 1, hj⟩).mpr rfl
        simpa only [List.get_eq_getElem, he] using hh

/-- The order-defined parent relation is exactly the immutable linked list
used by the verified machine initialization. -/
theorem records_iff (xs : List α) (r : α → Nat)
    (hs : xs.Pairwise (fun p q => r p < r q)) (f : α → β)
    (p : α) (a : β) (parent : Option α) :
    (p, a, parent) ∈ records (xs.map (fun q => (q, f q))) ↔
      p ∈ xs ∧ a = f p ∧ Parent xs r p parent := by
  rw [records_map_mem]
  constructor
  · rintro ⟨i, rfl, ha, hp⟩
    exact ⟨List.get_mem _ _, ha, (parent_get xs r hs i parent).mpr hp⟩
  · rintro ⟨hp, ha, hparent⟩
    obtain ⟨i, rfl⟩ := List.get_of_mem hp
    exact ⟨i, rfl, ha, (parent_get xs r hs i parent).mp hparent⟩

theorem head_iff (xs : List α) (r : α → Nat)
    (hs : xs.Pairwise (fun p q => r p < r q)) (f : α → β) (p : α) :
    head (xs.map (fun q => (q, f q))) = some p ↔ First xs r p := by
  rw [head_map, List.head?_eq_getElem?]
  constructor
  · intro h
    obtain ⟨hi, he⟩ := List.getElem?_eq_some_iff.mp h
    have hh := (first_get xs r hs ⟨0, hi⟩).mpr rfl
    simpa only [List.get_eq_getElem, he] using hh
  · intro h
    obtain ⟨i, hi, hiz⟩ := (first_iff xs r hs p).mp h
    rw [← hiz, List.getElem?_eq_getElem i.isLt]
    exact congrArg some hi

end Lax751879Proofs.OrderedRecords
