import Mathlib.Data.Set.Insert
import Mathlib.Data.List.Basic

namespace Lax979537Proofs.PersistentStack

variable {Node Symbol : Type}

abbrev Heap (Node Symbol : Type) := Set (Node × Symbol × Option Node)

def Functional (H : Heap Node Symbol) : Prop :=
  ∀ n a p b q, (n, a, p) ∈ H → (n, b, q) ∈ H → a = b ∧ p = q

def Fresh (H : Heap Node Symbol) (n : Node) : Prop := ∀ a p, (n, a, p) ∉ H

/-- A finite stack is represented by a chain of immutable node records. -/
inductive Chain (H : Heap Node Symbol) : Option Node → List Symbol → Prop
  | nil : Chain H none []
  | cons {n a p xs} : (n, a, p) ∈ H → Chain H p xs → Chain H (some n) (a :: xs)

theorem Chain.mono {H G : Heap Node Symbol} (hHG : H ⊆ G) {p : Option Node} {xs : List Symbol}
    (h : Chain H p xs) : Chain G p xs := by
  induction h with
  | nil => exact .nil
  | cons hr _ ih => exact .cons (hHG hr) ih

theorem Chain.unique {H : Heap Node Symbol} (hH : Functional H) {p : Option Node} {xs ys : List Symbol}
    (hx : Chain H p xs) (hy : Chain H p ys) : xs = ys := by
  induction hx generalizing ys with
  | nil => cases hy; rfl
  | @cons n a p xs hr hx ih =>
      cases hy with
      | @cons _ b q ys hs hy =>
          obtain ⟨rfl, rfl⟩ := hH n a p b q hr hs
          exact congrArg (a :: ·) (ih hy)

theorem Chain.none_iff {H : Heap Node Symbol} {xs : List Symbol} : Chain H none xs ↔ xs = [] := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .nil

theorem Chain.nil_iff {H : Heap Node Symbol} {p : Option Node} : Chain H p [] ↔ p = none := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .nil

theorem Chain.some_iff {H : Heap Node Symbol} {n : Node} {xs : List Symbol} :
    Chain H (some n) xs ↔ ∃ a p ys, (n, a, p) ∈ H ∧ Chain H p ys ∧ xs = a :: ys := by
  constructor
  · intro h; cases h with | cons hr ht => exact ⟨_, _, _, hr, ht, rfl⟩
  · rintro ⟨a, p, ys, hr, ht, rfl⟩; exact .cons hr ht

theorem insert_functional {H : Heap Node Symbol} (hH : Functional H) {n : Node}
    (hn : Fresh H n) (a : Symbol) (p : Option Node) : Functional (insert (n, a, p) H) := by
  intro m b q c r hb hc
  rcases Set.mem_insert_iff.mp hb with he | hb
  · cases he
    rcases Set.mem_insert_iff.mp hc with he | hc
    · cases he; exact ⟨rfl, rfl⟩
    · exact False.elim (hn c r hc)
  · rcases Set.mem_insert_iff.mp hc with he | hc
    · cases he; exact False.elim (hn b q hb)
    · exact hH m b q c r hb hc

theorem push_chain {H : Heap Node Symbol} {p : Option Node} {xs : List Symbol}
    (h : Chain H p xs) (n : Node) (a : Symbol) : Chain (insert (n, a, p) H) (some n) (a :: xs) :=
  .cons (Set.mem_insert _ _) (h.mono (Set.subset_insert _ _))

/-- Positive lookup: the empty head is explicit, and a nonempty head uses
one node fact. No absence test on the heap is required. -/
def Read (H : Heap Node Symbol) (head : Option Node) (value : Option Symbol) (parent : Option Node) : Prop :=
  (head = none ∧ value = none ∧ parent = none) ∨
    ∃ n a, head = some n ∧ value = some a ∧ (n, a, parent) ∈ H

theorem Read.mono {H G : Heap Node Symbol} (hHG : H ⊆ G) {head parent : Option Node}
    {value : Option Symbol} (h : Read H head value parent) : Read G head value parent := by
  rcases h with he | ⟨n, a, hh, hv, hr⟩
  · exact Or.inl he
  · exact Or.inr ⟨n, a, hh, hv, hHG hr⟩

theorem Chain.read_exists {H : Heap Node Symbol} {head : Option Node} {xs : List Symbol}
    (h : Chain H head xs) : ∃ parent, Read H head xs.head? parent ∧ Chain H parent xs.tail := by
  cases h with
  | nil => exact ⟨none, Or.inl ⟨rfl, rfl, rfl⟩, .nil⟩
  | @cons n a p xs hr ht => exact ⟨p, Or.inr ⟨n, a, rfl, rfl, hr⟩, ht⟩

theorem read_correct {H : Heap Node Symbol} (hH : Functional H)
    {head parent : Option Node} {xs : List Symbol} {value : Option Symbol}
    (h : Chain H head xs) (hr : Read H head value parent) :
    value = xs.head? ∧ Chain H parent xs.tail := by
  rcases hr with ⟨rfl, rfl, rfl⟩ | ⟨n, a, rfl, rfl, hr⟩
  · cases h; exact ⟨rfl, .nil⟩
  · cases h with
    | @cons _ b q ys hs ht =>
        obtain ⟨rfl, rfl⟩ := hH n a parent b q hr hs
        exact ⟨rfl, ht⟩

theorem read_unique {H : Heap Node Symbol} (hH : Functional H) {head p q : Option Node}
    {a b : Option Symbol} (ha : Read H head a p) (hb : Read H head b q) : a = b ∧ p = q := by
  rcases ha with ⟨rfl, rfl, rfl⟩ | ⟨n, a, rfl, rfl, ha⟩
  · rcases hb with ⟨_, rfl, rfl⟩ | ⟨n, b, he, _, _⟩
    · exact ⟨rfl, rfl⟩
    · cases he
  · rcases hb with ⟨he, _, _⟩ | ⟨m, b, he, rfl, hb⟩
    · cases he
    · cases he
      obtain ⟨rfl, rfl⟩ := hH n a p b q ha hb
      exact ⟨rfl, rfl⟩

theorem read_map_correct {A : Type} (f : A → Symbol) (hf : Function.Injective f)
    {H : Heap Node Symbol} (hH : Functional H) {head parent : Option Node}
    {xs : List A} {value : Option A} (h : Chain H head (xs.map f))
    (hr : Read H head (value.map f) parent) :
    value = xs.head? ∧ Chain H parent (xs.tail.map f) := by
  obtain ⟨hv, ht⟩ := read_correct hH h hr
  rw [List.head?_map] at hv
  refine ⟨Option.map_injective hf hv, ?_⟩
  simpa only [List.map_tail] using ht

end Lax979537Proofs.PersistentStack
