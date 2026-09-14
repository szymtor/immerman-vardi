import Lax751879Proofs.TupleAddresses
import Lax751879Proofs.FormulaMacros

namespace Lax751879Proofs.AddressFormulas

open Lax751879.OrderedStructures Lax751879.FixedPointSyntax
open Lax751879.FixedPointSemantics
open TupleOrder TupleAddresses FormulaMacros

def first {σ : Vocabulary} {m k : Nat} {ρ : List Nat}
    (x : Fin k → Fin m) : RawFormula σ m ρ :=
  .neg (existsBlock k
    (lexFormula (Fin.castAdd m) (Fin.natAdd k ∘ x)))

def successor {σ : Vocabulary} {m k : Nat} {ρ : List Nat}
    (x y : Fin k → Fin m) : RawFormula σ m ρ :=
  .conj (lexFormula x y) (.neg (existsBlock k
    (.conj (lexFormula (Fin.natAdd k ∘ x) (Fin.castAdd m))
      (lexFormula (Fin.castAdd m) (Fin.natAdd k ∘ y)))))

theorem first_firstOrder {σ : Vocabulary} {m k : Nat} {ρ : List Nat}
    (x : Fin k → Fin m) : FirstOrder (first (σ := σ) (ρ := ρ) x) :=
  (firstOrder_existsBlock _ _).mpr (firstOrder_lex _ _)

theorem successor_firstOrder {σ : Vocabulary} {m k : Nat} {ρ : List Nat}
    (x y : Fin k → Fin m) : FirstOrder (successor (σ := σ) (ρ := ρ) x y) :=
  ⟨firstOrder_lex _ _, (firstOrder_existsBlock _ _).mpr
    ⟨firstOrder_lex _ _, firstOrder_lex _ _⟩⟩

theorem no_smaller_iff {N : Nat} (x : Fin N) :
    (¬∃ y : Fin N, y < x) ↔ x.val = 0 := by
  constructor
  · intro h
    by_contra hx
    exact h ⟨⟨0, by have := x.isLt; omega⟩, by change 0 < x.val; omega⟩
  · intro h ⟨y, hy⟩
    change y.val < x.val at hy
    omega

theorem no_between_iff {N : Nat} (x y : Fin N) :
    (x < y ∧ ¬∃ z : Fin N, x < z ∧ z < y) ↔ x.val + 1 = y.val := by
  constructor
  · rintro ⟨hxy, h⟩
    change x.val < y.val at hxy
    by_contra he
    have hz : x.val + 1 < N := by have := y.isLt; omega
    exact h ⟨⟨x.val + 1, hz⟩, by change x.val < x.val + 1; omega,
      by change x.val + 1 < y.val; omega⟩
  · intro h
    refine ⟨by change x.val < y.val; omega, ?_⟩
    rintro ⟨z, hxz, hzy⟩
    change x.val < z.val at hxz
    change z.val < y.val at hzy
    omega

theorem eval_first {σ : Vocabulary} {m k : Nat} {ρ : List Nat}
    (x : Fin k → Fin m) (A : OrderedStructure σ)
    (v : Fin m → Fin A.size) (η : RelationEnv A.size ρ) :
    eval (first x) A v η ↔ (address A.size k (v ∘ x)).val = 0 := by
  simp only [first, eval, eval_existsBlock, eval_lex_address]
  have hl : ∀ a : Fin k → Fin A.size, Fin.append a v ∘ Fin.castAdd m = a := by
    intro a; funext i; simp
  have hr : ∀ a : Fin k → Fin A.size,
      Fin.append a v ∘ (Fin.natAdd k ∘ x) = v ∘ x := by
    intro a; funext i; simp
  simp only [hl, hr]
  rw [← no_smaller_iff]
  apply not_congr
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨address A.size k a, ha⟩
  · rintro ⟨t, ht⟩
    exact ⟨(address A.size k).symm t, by simpa using ht⟩

theorem eval_successor {σ : Vocabulary} {m k : Nat} {ρ : List Nat}
    (x y : Fin k → Fin m) (A : OrderedStructure σ)
    (v : Fin m → Fin A.size) (η : RelationEnv A.size ρ) :
    eval (successor x y) A v η ↔
      (address A.size k (v ∘ x)).val + 1 = (address A.size k (v ∘ y)).val := by
  simp only [successor, eval, eval_existsBlock, eval_lex_address]
  have hl : ∀ a : Fin k → Fin A.size, Fin.append a v ∘ Fin.castAdd m = a := by
    intro a; funext i; simp
  have hr : ∀ (a : Fin k → Fin A.size) (z : Fin k → Fin m),
      Fin.append a v ∘ (Fin.natAdd k ∘ z) = v ∘ z := by
    intro a z; funext i; simp
  simp only [hl, hr]
  rw [← no_between_iff]
  apply and_congr_right
  intro _
  apply not_congr
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨address A.size k a, ha⟩
  · rintro ⟨t, ht⟩
    exact ⟨(address A.size k).symm t, by simpa using ht⟩

theorem address_one (n : Nat) (a : Fin 1 → Fin n) :
    (address n 1 a).val = (a 0).val := by
  rw [address_succ]
  have h := (address n 0 (Fin.tail a)).isLt
  simp only [pow_zero, Nat.one_mul] at *
  omega

/-- A fixed numeral is definable using order alone. On a domain too small
to contain it, the formula is false. -/
def numeral {σ : Vocabulary} {ρ : List Nat} (c : Nat) {m : Nat}
    (x : Fin m) : RawFormula σ m ρ :=
  match c with
  | 0 => first (fun _ : Fin 1 => x)
  | c + 1 => .exists' (.conj (numeral c 0)
      (successor (fun _ : Fin 1 => 0) (fun _ : Fin 1 => x.succ)))

theorem numeral_firstOrder {σ : Vocabulary} {ρ : List Nat} (c : Nat)
    {m : Nat} (x : Fin m) : FirstOrder (numeral (σ := σ) (ρ := ρ) c x) := by
  induction c generalizing m with
  | zero => exact first_firstOrder _
  | succ c ih => exact ⟨ih _, successor_firstOrder _ _⟩

theorem eval_numeral {σ : Vocabulary} {ρ : List Nat} (c : Nat) {m : Nat}
    (x : Fin m) (A : OrderedStructure σ)
    (v : Fin m → Fin A.size) (η : RelationEnv A.size ρ) :
    eval (numeral c x) A v η ↔ (v x).val = c := by
  induction c generalizing m with
  | zero => simpa only [numeral, address_one, Function.comp_apply] using
      eval_first (fun _ : Fin 1 => x) A v η
  | succ c ih =>
      simp only [numeral, eval, ih, eval_successor, address_one,
        Function.comp_apply, Fin.cons_zero, Fin.cons_succ]
      constructor
      · rintro ⟨a, ha, hv⟩
        omega
      · intro h
        exact ⟨⟨c, by have := (v x).isLt; omega⟩, rfl, h.symm⟩

def sizeAtMost {σ : Vocabulary} {m : Nat} {ρ : List Nat} (N : Nat) :
    RawFormula σ m ρ := .neg (.exists' (numeral N 0))

theorem eval_sizeAtMost {σ : Vocabulary} {m : Nat} {ρ : List Nat} (N : Nat)
    (A : OrderedStructure σ) (v : Fin m → Fin A.size) (η : RelationEnv A.size ρ) :
    eval (sizeAtMost N) A v η ↔ A.size ≤ N := by
  simp only [sizeAtMost, eval, eval_numeral, Fin.cons_zero]
  constructor
  · intro h
    by_contra hN
    exact h ⟨⟨N, by omega⟩, rfl⟩
  · intro h ⟨a, ha⟩
    have := a.isLt
    omega

def sizeExactly {σ : Vocabulary} {m : Nat} {ρ : List Nat} (N : Nat) :
    RawFormula σ m ρ :=
  .conj (sizeAtMost N) (match N with | 0 => .truth | n + 1 => .neg (sizeAtMost n))

theorem sizeExactly_firstOrder {σ : Vocabulary} {m : Nat} {ρ : List Nat}
    (N : Nat) : FirstOrder (sizeExactly (σ := σ) (m := m) (ρ := ρ) N) := by
  cases N with
  | zero => exact ⟨numeral_firstOrder _ _, trivial⟩
  | succ n => exact ⟨numeral_firstOrder _ _, numeral_firstOrder _ _⟩

theorem eval_sizeExactly {σ : Vocabulary} {m : Nat} {ρ : List Nat} (N : Nat)
    (A : OrderedStructure σ) (v : Fin m → Fin A.size) (η : RelationEnv A.size ρ) :
    eval (sizeExactly N) A v η ↔ A.size = N := by
  cases N with
  | zero =>
      change (eval (sizeAtMost 0) A v η ∧ True) ↔ A.size = 0
      rw [eval_sizeAtMost]
      simp
  | succ n =>
      change (eval (sizeAtMost (n + 1)) A v η ∧ ¬eval (sizeAtMost n) A v η) ↔ _
      rw [eval_sizeAtMost, eval_sizeAtMost]
      omega

end Lax751879Proofs.AddressFormulas
