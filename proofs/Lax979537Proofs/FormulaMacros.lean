import Lax979537Proofs.TupleOrder

namespace Lax979537Proofs.FormulaMacros

open Lax979537.OrderedStructures Lax979537.FixedPointSyntax
open Lax979537.FixedPointSemantics
open SyntaxOperations TupleOrder

/-- The first-order fragment, without free relation variables. -/
def FirstOrder {σ : Vocabulary} {m : Nat} {ρ : List Nat} :
    RawFormula σ m ρ → Prop
  | .truth | .equal _ _ | .less _ _ | .relation _ _ => True
  | .variable _ _ | .lfp _ _ _ => False
  | .neg φ | .exists' φ => FirstOrder φ
  | .conj φ ψ => FirstOrder φ ∧ FirstOrder ψ

theorem firstOrder_admissible {σ : Vocabulary} {m : Nat} {ρ : List Nat}
    (φ : RawFormula σ m ρ) (h : FirstOrder φ) : φ.Admissible := by
  induction φ with
  | truth | equal | less | relation => trivial
  | «variable» | lfp => exact h.elim
  | neg ψ ih | exists' ψ ih => exact ih h
  | conj ψ χ ihψ ihχ => exact ⟨ihψ h.1, ihχ h.2⟩

theorem firstOrder_rename {σ : Vocabulary} {m : Nat} {ρ : List Nat}
    (φ : RawFormula σ m ρ) {l : Nat} (f : Fin m → Fin l) :
    FirstOrder (rename φ f) ↔ FirstOrder φ := by
  induction φ generalizing l with
  | truth | equal | less | relation | «variable» | lfp => rfl
  | neg ψ ih | exists' ψ ih => exact ih _
  | conj ψ χ ihψ ihχ => exact and_congr (ihψ _) (ihχ _)

theorem firstOrder_allOf {σ : Vocabulary} {m : Nat} {ρ : List Nat}
    (fs : List (RawFormula σ m ρ)) :
    FirstOrder (allOf fs) ↔ ∀ φ ∈ fs, FirstOrder φ := by
  induction fs with
  | nil => simp [allOf, FirstOrder]
  | cons φ fs ih => simp [allOf, FirstOrder, ih]

theorem firstOrder_anyOf {σ : Vocabulary} {m : Nat} {ρ : List Nat}
    (fs : List (RawFormula σ m ρ)) :
    FirstOrder (anyOf fs) ↔ ∀ φ ∈ fs, FirstOrder φ := by
  induction fs with
  | nil => simp [anyOf, FirstOrder]
  | cons φ fs ih => simp [anyOf, disj, FirstOrder, ih]

theorem firstOrder_lex {σ : Vocabulary} {m k : Nat} {ρ : List Nat}
    (x y : Fin k → Fin m) : FirstOrder (lexFormula (σ := σ) (ρ := ρ) x y) := by
  simp only [lexFormula, firstOrder_anyOf, List.forall_mem_map, List.mem_finRange,
    forall_const, FirstOrder, true_and, firstOrder_allOf]
  intro i j
  by_cases h : j < i <;> simp [h, FirstOrder]

/-- Copy a first-order formula into a new relation-variable context.
The correctness theorem requires `FirstOrder`; the other branches are
unreachable under that hypothesis. -/
def copyFO {σ : Vocabulary} {m : Nat} {ρ : List Nat}
    (φ : RawFormula σ m ρ) (τ : List Nat) : RawFormula σ m τ :=
  match φ with
  | .truth => .truth
  | .equal x y => .equal x y
  | .less x y => .less x y
  | .relation r args => .relation r args
  | .variable _ _ | .lfp _ _ _ => .truth
  | .neg ψ => .neg (copyFO ψ τ)
  | .conj ψ χ => .conj (copyFO ψ τ) (copyFO χ τ)
  | .exists' ψ => .exists' (copyFO ψ τ)

theorem copyFO_admissible {σ : Vocabulary} {m : Nat} {ρ : List Nat}
    (φ : RawFormula σ m ρ) (τ : List Nat) : (copyFO φ τ).Admissible := by
  induction φ with
  | truth | equal | less | relation | «variable» | lfp => trivial
  | neg ψ ih | exists' ψ ih => exact ih
  | conj ψ χ ihψ ihχ => exact ⟨ihψ, ihχ⟩

theorem copyFO_positive {σ : Vocabulary} {m : Nat} {ρ : List Nat}
    (φ : RawFormula σ m ρ) (τ : List Nat) (r : Fin τ.length) (p : Bool) :
    (copyFO φ τ).positiveAt r p := by
  induction φ generalizing p with
  | truth | equal | less | relation | «variable» | lfp => trivial
  | neg ψ ih => exact ih (!p)
  | exists' ψ ih => exact ih p
  | conj ψ χ ihψ ihχ => exact ⟨ihψ p, ihχ p⟩

theorem eval_copyFO {σ : Vocabulary} {m : Nat} {ρ : List Nat}
    (φ : RawFormula σ m ρ) (h : FirstOrder φ) (τ : List Nat)
    (A : OrderedStructure σ) (v : Fin m → Fin A.size)
    (η : RelationEnv A.size ρ) (ζ : RelationEnv A.size τ) :
    eval (copyFO φ τ) A v ζ ↔ eval φ A v η := by
  induction φ with
  | truth | equal | less | relation => rfl
  | «variable» | lfp => exact h.elim
  | neg ψ ih => exact not_congr (ih h v η)
  | conj ψ χ ihψ ihχ => exact and_congr (ihψ h.1 v η) (ihχ h.2 v η)
  | exists' ψ ih => exact exists_congr (fun a => ih h (Fin.cons a v) η)

/-- Existentially bind a block at the front of the element-variable context. -/
def existsBlock {σ : Vocabulary} {ρ : List Nat} (k : Nat) {m : Nat} :
    RawFormula σ (k + m) ρ → RawFormula σ m ρ :=
  match k with
  | 0 => fun φ => rename φ (Fin.cast (Nat.zero_add m))
  | k + 1 => fun φ => existsBlock k
      (.exists' (rename φ (Fin.cast (Nat.add_right_comm k 1 m))))

theorem existsBlock_admissible {σ : Vocabulary} {ρ : List Nat} (k : Nat)
    {m : Nat} (φ : RawFormula σ (k + m) ρ) :
    (existsBlock k φ).Admissible ↔ φ.Admissible := by
  induction k with
  | zero => exact rename_admissible _ _
  | succ k ih =>
      exact (ih _).trans (rename_admissible φ _)

theorem existsBlock_positive {σ : Vocabulary} {ρ : List Nat} (k : Nat)
    {m : Nat} (φ : RawFormula σ (k + m) ρ) (r : Fin ρ.length) (p : Bool) :
    (existsBlock k φ).positiveAt r p ↔ φ.positiveAt r p := by
  induction k with
  | zero => exact rename_positiveAt _ _ _ _
  | succ k ih => exact (ih _).trans (rename_positiveAt φ _ r p)

theorem firstOrder_existsBlock {σ : Vocabulary} {ρ : List Nat} (k : Nat)
    {m : Nat} (φ : RawFormula σ (k + m) ρ) :
    FirstOrder (existsBlock k φ) ↔ FirstOrder φ := by
  induction k with
  | zero => exact firstOrder_rename _ _
  | succ k ih => exact (ih _).trans (firstOrder_rename φ _)

theorem eval_existsBlock {σ : Vocabulary} {ρ : List Nat} (k : Nat)
    {m : Nat} (φ : RawFormula σ (k + m) ρ) (A : OrderedStructure σ)
    (v : Fin m → Fin A.size) (η : RelationEnv A.size ρ) :
    eval (existsBlock k φ) A v η ↔
      ∃ a : Fin k → Fin A.size, eval φ A (Fin.append a v) η := by
  induction k with
  | zero =>
      rw [existsBlock, eval_rename]
      constructor
      · intro h
        exact ⟨Fin.elim0, by simpa only [Fin.elim0_append] using h⟩
      · rintro ⟨a, ha⟩
        have he : a = Fin.elim0 := Subsingleton.elim _ _
        simpa only [he, Fin.elim0_append] using ha
  | succ k ih =>
      rw [existsBlock, ih]
      simp only [eval, eval_rename]
      constructor
      · rintro ⟨b, a, h⟩
        exact ⟨Fin.cons a b, by simpa only [Fin.append_cons] using h⟩
      · rintro ⟨a, h⟩
        refine ⟨Fin.tail a, a 0, ?_⟩
        simpa only [← Fin.append_cons, Fin.cons_self_tail] using h

theorem positive_allOf {σ : Vocabulary} {m : Nat} {ρ : List Nat}
    (fs : List (RawFormula σ m ρ)) (r : Fin ρ.length) (p : Bool) :
    (allOf fs).positiveAt r p ↔ ∀ φ ∈ fs, φ.positiveAt r p := by
  induction fs with
  | nil => simp [allOf, RawFormula.positiveAt]
  | cons φ fs ih => simp [allOf, RawFormula.positiveAt, ih]

theorem positive_anyOf {σ : Vocabulary} {m : Nat} {ρ : List Nat}
    (fs : List (RawFormula σ m ρ)) (r : Fin ρ.length) (p : Bool) :
    (anyOf fs).positiveAt r p ↔ ∀ φ ∈ fs, φ.positiveAt r p := by
  induction fs with
  | nil => simp [anyOf, RawFormula.positiveAt]
  | cons φ fs ih => simp [anyOf, disj, RawFormula.positiveAt, ih]

end Lax979537Proofs.FormulaMacros
