import Lax979537Proofs.InputOrder
import Lax979537Proofs.InputPositionFormulas
import Lax979537Proofs.SortedLinks

namespace Lax979537Proofs.InputLinkFormulas

open Lax979537.OrderedStructures Lax979537.FixedPointSyntax
open Lax979537.FixedPointSemantics
open InputSegments InputTupleCodes InputOrder InputPositionFormulas FormulaMacros TupleOrder

/-- Existence of a valid input position between optional strict bounds. -/
def window {σ : Vocabulary} {m v w : Nat} {ρ : List Nat}
    (hw : ∀ s : Segment σ m, s.arity ≤ w) (query : Fin m → Fin v)
    (lo hi : Option (Fin (w + 1) → Fin v)) : RawFormula σ v ρ :=
  existsBlock (w + 1)
    (.conj (position hw (Fin.natAdd (w + 1) ∘ query) (Fin.castAdd v))
      (.conj (match lo with
        | none => .truth
        | some x => lexFormula (Fin.natAdd (w + 1) ∘ x) (Fin.castAdd v))
        (match hi with
        | none => .truth
        | some x => lexFormula (Fin.castAdd v) (Fin.natAdd (w + 1) ∘ x))))

theorem window_firstOrder {σ : Vocabulary} {m v w : Nat} {ρ : List Nat}
    (hw : ∀ s : Segment σ m, s.arity ≤ w) (query : Fin m → Fin v)
    (lo hi : Option (Fin (w + 1) → Fin v)) : FirstOrder (window (ρ := ρ) hw query lo hi) := by
  apply (firstOrder_existsBlock _ _).mpr
  refine ⟨position_firstOrder _ _ _, ?_, ?_⟩
  · cases lo with
    | none => trivial
    | some x => exact firstOrder_lex _ _
  · cases hi with
    | none => trivial
    | some x => exact firstOrder_lex _ _

theorem eval_window {σ : Vocabulary} {m v w : Nat} {ρ : List Nat}
    (hw : ∀ s : Segment σ m, s.arity ≤ w) (query : Fin m → Fin v)
    (lo hi : Option (Fin (w + 1) → Fin v)) (A : OrderedStructure σ)
    (hn : tagBound σ m ≤ A.size) (a : Fin v → Fin A.size) (η : RelationEnv A.size ρ) :
    eval (window hw query lo hi) A a η ↔
      ∃ p ∈ positions ⟨A, a ∘ query⟩,
        (lo.elim True (fun x => TupleLex (a ∘ x) (code hn hw p))) ∧
        (hi.elim True (fun x => TupleLex (code hn hw p) (a ∘ x))) := by
  have hv : ∀ b : Fin (w + 1) → Fin A.size, Fin.append b a ∘ Fin.castAdd v = b := by
    intro b; funext i; simp
  have hr : ∀ b : Fin (w + 1) → Fin A.size,
      Fin.append b a ∘ Fin.natAdd (w + 1) = a := by
    intro b; funext i; simp
  have hP : ∀ b : Fin (w + 1) → Fin A.size,
      positions (⟨A, (Fin.append b a ∘ Fin.natAdd (w + 1)) ∘ query⟩ : PointedStructure σ m) =
        positions ⟨A, a ∘ query⟩ := by
    intro b
    rw [hr]
  cases lo <;> cases hi <;>
    simp only [window, eval_existsBlock, eval, eval_position hw _ _ A hn,
      eval_lexFormula, ← Function.comp_assoc, hv, hr, hP, Option.elim_none, Option.elim_some]
  all_goals constructor
  all_goals first
    | (rintro ⟨b, ⟨p, hp, hc⟩, hl, hu⟩; subst b; exact ⟨p, hp, hl, hu⟩)
    | (rintro ⟨p, hp, hl, hu⟩; exact ⟨code hn hw p, ⟨p, hp, rfl⟩, hl, hu⟩)

def first {σ : Vocabulary} {m v w : Nat} {ρ : List Nat}
    (hw : ∀ s : Segment σ m, s.arity ≤ w) (query : Fin m → Fin v)
    (x : Fin (w + 1) → Fin v) : RawFormula σ v ρ :=
  .conj (position hw query x) (.neg (window hw query none (some x)))

def last {σ : Vocabulary} {m v w : Nat} {ρ : List Nat}
    (hw : ∀ s : Segment σ m, s.arity ≤ w) (query : Fin m → Fin v)
    (x : Fin (w + 1) → Fin v) : RawFormula σ v ρ :=
  .conj (position hw query x) (.neg (window hw query (some x) none))

def next {σ : Vocabulary} {m v w : Nat} {ρ : List Nat}
    (hw : ∀ s : Segment σ m, s.arity ≤ w) (query : Fin m → Fin v)
    (x y : Fin (w + 1) → Fin v) : RawFormula σ v ρ :=
  .conj (position hw query x) (.conj (position hw query y)
    (.conj (lexFormula x y) (.neg (window hw query (some x) (some y)))))

theorem first_firstOrder {σ : Vocabulary} {m v w : Nat} {ρ : List Nat}
    (hw : ∀ s : Segment σ m, s.arity ≤ w) (query : Fin m → Fin v)
    (x : Fin (w + 1) → Fin v) : FirstOrder (first (ρ := ρ) hw query x) :=
  ⟨position_firstOrder _ _ _, window_firstOrder _ _ _ _⟩

theorem last_firstOrder {σ : Vocabulary} {m v w : Nat} {ρ : List Nat}
    (hw : ∀ s : Segment σ m, s.arity ≤ w) (query : Fin m → Fin v)
    (x : Fin (w + 1) → Fin v) : FirstOrder (last (ρ := ρ) hw query x) :=
  ⟨position_firstOrder _ _ _, window_firstOrder _ _ _ _⟩

theorem next_firstOrder {σ : Vocabulary} {m v w : Nat} {ρ : List Nat}
    (hw : ∀ s : Segment σ m, s.arity ≤ w) (query : Fin m → Fin v)
    (x y : Fin (w + 1) → Fin v) : FirstOrder (next (ρ := ρ) hw query x y) :=
  ⟨position_firstOrder _ _ _, position_firstOrder _ _ _, firstOrder_lex _ _, window_firstOrder _ _ _ _⟩

theorem eval_position_coded {σ : Vocabulary} {m v w : Nat} {ρ : List Nat}
    (hw : ∀ s : Segment σ m, s.arity ≤ w) (query : Fin m → Fin v)
    (x : Fin (w + 1) → Fin v) (A : OrderedStructure σ)
    (hn : tagBound σ m ≤ A.size) (a : Fin v → Fin A.size) (η : RelationEnv A.size ρ)
    (p : Identifier σ m A.size) (hc : code hn hw p = a ∘ x) :
    eval (position hw query x) A a η ↔ p ∈ positions ⟨A, a ∘ query⟩ := by
  rw [eval_position hw query x A hn, ← hc]
  constructor
  · rintro ⟨q, hq, he⟩
    exact (code_injective hn hw he) ▸ hq
  · intro hp; exact ⟨p, hp, rfl⟩

theorem code_lex_iff {σ : Vocabulary} {m w : Nat} (A : PointedStructure σ m)
    (hn : tagBound σ m ≤ A.structureValue.size) (hw : ∀ s : Segment σ m, s.arity ≤ w)
    (p q : Identifier σ m A.structureValue.size) :
    TupleLex (code hn hw p) (code hn hw q) ↔ rank A hn hw p < rank A hn hw q :=
  (TupleAddresses.address_lt_iff _ _ _ _).symm

theorem eval_first_coded {σ : Vocabulary} {m v w : Nat} {ρ : List Nat}
    (hw : ∀ s : Segment σ m, s.arity ≤ w) (query : Fin m → Fin v)
    (x : Fin (w + 1) → Fin v) (A : OrderedStructure σ)
    (hn : tagBound σ m ≤ A.size) (a : Fin v → Fin A.size) (η : RelationEnv A.size ρ)
    (p : Identifier σ m A.size) (hc : code hn hw p = a ∘ x) :
    eval (first hw query x) A a η ↔
      SortedLinks.First (positions ⟨A, a ∘ query⟩) (rank ⟨A, a ∘ query⟩ hn hw) p := by
  simp only [first, eval, eval_position_coded hw query x A hn a η p hc,
    eval_window hw query _ _ A hn, Option.elim_none, Option.elim_some,
    ← hc, true_and, code_lex_iff ⟨A, a ∘ query⟩ hn hw, SortedLinks.First]

theorem eval_last_coded {σ : Vocabulary} {m v w : Nat} {ρ : List Nat}
    (hw : ∀ s : Segment σ m, s.arity ≤ w) (query : Fin m → Fin v)
    (x : Fin (w + 1) → Fin v) (A : OrderedStructure σ)
    (hn : tagBound σ m ≤ A.size) (a : Fin v → Fin A.size) (η : RelationEnv A.size ρ)
    (p : Identifier σ m A.size) (hc : code hn hw p = a ∘ x) :
    eval (last hw query x) A a η ↔
      SortedLinks.Last (positions ⟨A, a ∘ query⟩) (rank ⟨A, a ∘ query⟩ hn hw) p := by
  simp only [last, eval, eval_position_coded hw query x A hn a η p hc,
    eval_window hw query _ _ A hn, Option.elim_none, Option.elim_some,
    ← hc, and_true, code_lex_iff ⟨A, a ∘ query⟩ hn hw, SortedLinks.Last]

theorem eval_next_coded {σ : Vocabulary} {m v w : Nat} {ρ : List Nat}
    (hw : ∀ s : Segment σ m, s.arity ≤ w) (query : Fin m → Fin v)
    (x y : Fin (w + 1) → Fin v) (A : OrderedStructure σ)
    (hn : tagBound σ m ≤ A.size) (a : Fin v → Fin A.size) (η : RelationEnv A.size ρ)
    (p q : Identifier σ m A.size) (hp : code hn hw p = a ∘ x) (hq : code hn hw q = a ∘ y) :
    eval (next hw query x y) A a η ↔
      SortedLinks.Next (positions ⟨A, a ∘ query⟩) (rank ⟨A, a ∘ query⟩ hn hw) p q := by
  simp only [next, eval, eval_position_coded hw query x A hn a η p hp,
    eval_position_coded hw query y A hn a η q hq,
    eval_window hw query _ _ A hn, Option.elim_some, eval_lexFormula,
    ← hp, ← hq, code_lex_iff ⟨A, a ∘ query⟩ hn hw, SortedLinks.Next]

theorem eval_first {σ : Vocabulary} {m v w : Nat} {ρ : List Nat}
    (hw : ∀ s : Segment σ m, s.arity ≤ w) (query : Fin m → Fin v)
    (x : Fin (w + 1) → Fin v) (A : OrderedStructure σ)
    (hn : tagBound σ m ≤ A.size) (a : Fin v → Fin A.size) (η : RelationEnv A.size ρ) :
    eval (first hw query x) A a η ↔ ∃ p, code hn hw p = a ∘ x ∧
      SortedLinks.First (positions ⟨A, a ∘ query⟩) (rank ⟨A, a ∘ query⟩ hn hw) p := by
  constructor
  · intro h
    obtain ⟨p, _, hc⟩ := (eval_position hw query x A hn a η).mp h.1
    exact ⟨p, hc, (eval_first_coded hw query x A hn a η p hc).mp h⟩
  · rintro ⟨p, hc, hp⟩
    exact (eval_first_coded hw query x A hn a η p hc).mpr hp

theorem eval_last {σ : Vocabulary} {m v w : Nat} {ρ : List Nat}
    (hw : ∀ s : Segment σ m, s.arity ≤ w) (query : Fin m → Fin v)
    (x : Fin (w + 1) → Fin v) (A : OrderedStructure σ)
    (hn : tagBound σ m ≤ A.size) (a : Fin v → Fin A.size) (η : RelationEnv A.size ρ) :
    eval (last hw query x) A a η ↔ ∃ p, code hn hw p = a ∘ x ∧
      SortedLinks.Last (positions ⟨A, a ∘ query⟩) (rank ⟨A, a ∘ query⟩ hn hw) p := by
  constructor
  · intro h
    obtain ⟨p, _, hc⟩ := (eval_position hw query x A hn a η).mp h.1
    exact ⟨p, hc, (eval_last_coded hw query x A hn a η p hc).mp h⟩
  · rintro ⟨p, hc, hp⟩
    exact (eval_last_coded hw query x A hn a η p hc).mpr hp

theorem eval_next {σ : Vocabulary} {m v w : Nat} {ρ : List Nat}
    (hw : ∀ s : Segment σ m, s.arity ≤ w) (query : Fin m → Fin v)
    (x y : Fin (w + 1) → Fin v) (A : OrderedStructure σ)
    (hn : tagBound σ m ≤ A.size) (a : Fin v → Fin A.size) (η : RelationEnv A.size ρ) :
    eval (next hw query x y) A a η ↔ ∃ p q,
      code hn hw p = a ∘ x ∧ code hn hw q = a ∘ y ∧
      SortedLinks.Next (positions ⟨A, a ∘ query⟩) (rank ⟨A, a ∘ query⟩ hn hw) p q := by
  constructor
  · intro h
    obtain ⟨p, _, hp⟩ := (eval_position hw query x A hn a η).mp h.1
    obtain ⟨q, _, hq⟩ := (eval_position hw query y A hn a η).mp h.2.1
    exact ⟨p, q, hp, hq, (eval_next_coded hw query x y A hn a η p q hp hq).mp h⟩
  · rintro ⟨p, q, hp, hq, h⟩
    exact (eval_next_coded hw query x y A hn a η p q hp hq).mpr h

end Lax979537Proofs.InputLinkFormulas
