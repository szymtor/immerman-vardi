import Lax979537Proofs.InitialPatterns
import Lax979537Proofs.InputBitFormulas
import Lax979537Proofs.InputLinkFormulas

namespace Lax979537Proofs.InitialNodeRules

open Turing Lax979537.OrderedStructures Lax979537.FixedPointSyntax Lax979537.FixedPointSemantics
open RuleConstants

@[reducible] def iWidth (σ : Vocabulary) := InputTupleCodes.width σ + 1
@[reducible] def numVars (σ : Vocabulary) (m : Nat) := m + (iWidth σ + iWidth σ)
def query (σ : Vocabulary) (m : Nat) : Fin m → Fin (numVars σ m) := Fin.castAdd _
def left (σ : Vocabulary) (m : Nat) : Fin (iWidth σ) → Fin (numVars σ m) := Fin.natAdd m ∘ Fin.castAdd _
def right (σ : Vocabulary) (m : Nat) : Fin (iWidth σ) → Fin (numVars σ m) := Fin.natAdd m ∘ Fin.natAdd (iWidth σ)

def data {σ : Vocabulary} {m n : Nat} (q : Fin m → Fin n) (x y : Fin (iWidth σ) → Fin n) :
    Fin (numVars σ m) → Fin n := Fin.append q (Fin.append x y)

@[simp] theorem data_query {σ : Vocabulary} {m n : Nat} (q : Fin m → Fin n) (x y : Fin (iWidth σ) → Fin n) :
    data q x y ∘ query σ m = q := by funext i; simp [data, query]
@[simp] theorem data_left {σ : Vocabulary} {m n : Nat} (q : Fin m → Fin n) (x y : Fin (iWidth σ) → Fin n) :
    data q x y ∘ left σ m = x := by funext i; simp [data, left]
@[simp] theorem data_right {σ : Vocabulary} {m n : Nat} (q : Fin m → Fin n) (x y : Fin (iWidth σ) → Fin n) :
    data q x y ∘ right σ m = y := by
  funext i
  simp only [data, right, Function.comp_apply, Fin.append_right]

def guard (σ : Vocabulary) (m : Nat) (bit terminal : Bool) : RawFormula σ (numVars σ m) [] :=
  .conj (InputBitFormulas.hasBit InputTupleCodes.arity_le_width (query σ m) (left σ m) bit)
    (if terminal then InputLinkFormulas.last InputTupleCodes.arity_le_width (query σ m) (left σ m)
     else InputLinkFormulas.next InputTupleCodes.arity_le_width (query σ m) (left σ m) (right σ m))

theorem guard_firstOrder (σ : Vocabulary) (m : Nat) (bit terminal : Bool) : FormulaMacros.FirstOrder (guard σ m bit terminal) := by
  refine ⟨InputBitFormulas.hasBit_firstOrder _ _ _ _, ?_⟩
  cases terminal
  · exact InputLinkFormulas.next_firstOrder _ _ _ _
  · exact InputLinkFormulas.last_firstOrder _ _ _

noncomputable def pattern (tm : FinTM2) (e : tm.Γ tm.k₀ ≃ Bool) (σ : Vocabulary) (m d w : Nat) (bit terminal : Bool) :
    Fin (FactCodes.payloadWidth tm d w + 1) → Fin (MachineConstants.bound tm + numVars σ m) :=
  InitialPatterns.node tm d (Fin.castAdd _ (MachineConstants.numeral tm 0))
    (Fin.castAdd _ (MachineConstants.numeral tm 1))
    (Fin.castAdd _ (MachineConstants.symbol tm (Sigma.mk tm.k₀ (e.symm bit)))) terminal
    (Fin.natAdd _ ∘ left σ m) (Fin.natAdd _ ∘ right σ m)

noncomputable def rule (tm : FinTM2) (e : tm.Γ tm.k₀ ≃ Bool) (σ : Vocabulary) (m d w : Nat) (bit terminal : Bool) :
    Template σ m (FactCodes.payloadWidth tm d w + 1) (MachineConstants.bound tm) where
  numVars := numVars σ m
  guard := guard σ m bit terminal
  guard_firstOrder := guard_firstOrder σ m bit terminal
  parameters := query σ m
  head := pattern tm e σ m d w bit terminal
  premises := []

noncomputable def value {tm : FinTM2} (e : tm.Γ tm.k₀ ≃ Bool) {n iWidth d w : Nat}
    (hn : MachineConstants.bound tm ≤ n) (bit terminal : Bool) (x y : Fin iWidth → Fin n) :
    Fin (FactCodes.payloadWidth tm d w + 1) → Fin n :=
  InitialPatterns.node tm d ⟨0, by have := MachineConstants.enough tm; omega⟩
    ⟨1, by have := MachineConstants.enough tm; omega⟩
    (SupportedCodes.code _ ((MachineConstants.symbols_bound tm).trans hn) (Sigma.mk tm.k₀ (e.symm bit))) terminal x y

theorem assignment_pattern {tm : FinTM2} (e : tm.Γ tm.k₀ ≃ Bool) {σ : Vocabulary} {m n d w : Nat}
    (hn : MachineConstants.bound tm ≤ n) (a : Fin (numVars σ m) → Fin n) (bit terminal : Bool) :
    assignment hn a ∘ pattern tm e σ m d w bit terminal =
      value (d := d) (w := w) e hn bit terminal (a ∘ left σ m) (a ∘ right σ m) := by
  rw [pattern, InitialPatterns.map_node]
  have hd (z : Fin (iWidth σ) → Fin (numVars σ m)) :
      assignment hn a ∘ (Fin.natAdd _ ∘ z) = a ∘ z := by funext i; simp [assignment]
  rw [hd, hd]
  simp only [assignment, Fin.append_left]
  rfl

theorem value_code {tm : FinTM2} (e : tm.Γ tm.k₀ ≃ Bool) {Initial : Type} {n iWidth d w : Nat}
    (P : FactCodes.Parameters tm Initial n iWidth d w) (hn : MachineConstants.bound tm ≤ n)
    (bit terminal : Bool) (p q : Initial) :
    value (d := d) (w := w) e hn bit terminal (P.initial p) (P.initial q) =
      FactCodes.code P (.node (.inl p, Sigma.mk tm.k₀ (e.symm bit), if terminal then none else some (.inl q))) := by
  cases terminal with
  | false =>
      dsimp only [value, InitialPatterns.node, InitialPatterns.parent, Bool.false_eq_true, ↓reduceIte]
      rw [InitialPatterns.initial_code P p, InitialPatterns.initial_code P q]
      rfl
  | true =>
      dsimp only [value, InitialPatterns.node, InitialPatterns.parent, ↓reduceIte]
      rw [InitialPatterns.initial_code P p, ← EmptyHead.code_none (d := d) (w := w) P.enough P.initial]
      rfl

end Lax979537Proofs.InitialNodeRules
