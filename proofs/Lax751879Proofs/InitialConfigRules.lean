import Lax751879Proofs.InitialNodeRules

namespace Lax751879Proofs.InitialConfigRules

open Turing Lax751879.OrderedStructures RuleConstants

@[reducible] def numVars (σ : Vocabulary) (m d : Nat) := m + (d + InitialNodeRules.iWidth σ)
def query (σ : Vocabulary) (m d : Nat) : Fin m → Fin (numVars σ m d) := Fin.castAdd _
def time (σ : Vocabulary) (m d : Nat) : Fin d → Fin (numVars σ m d) := Fin.natAdd m ∘ Fin.castAdd _
def position (σ : Vocabulary) (m d : Nat) : Fin (InitialNodeRules.iWidth σ) → Fin (numVars σ m d) :=
  Fin.natAdd m ∘ Fin.natAdd d

def data {σ : Vocabulary} {m d n : Nat} (q : Fin m → Fin n) (t : Fin d → Fin n)
    (p : Fin (InitialNodeRules.iWidth σ) → Fin n) : Fin (numVars σ m d) → Fin n :=
  Fin.append q (Fin.append t p)

@[simp] theorem data_query {σ : Vocabulary} {m d n : Nat} (q : Fin m → Fin n) (t : Fin d → Fin n)
    (p : Fin (InitialNodeRules.iWidth σ) → Fin n) : data q t p ∘ query σ m d = q := by
  funext i; simp only [data, query, Function.comp_apply, Fin.append_left]
@[simp] theorem data_time {σ : Vocabulary} {m d n : Nat} (q : Fin m → Fin n) (t : Fin d → Fin n)
    (p : Fin (InitialNodeRules.iWidth σ) → Fin n) : data q t p ∘ time σ m d = t := by
  funext i; simp only [data, time, Function.comp_apply, Fin.append_left, Fin.append_right]
@[simp] theorem data_position {σ : Vocabulary} {m d n : Nat} (q : Fin m → Fin n) (t : Fin d → Fin n)
    (p : Fin (InitialNodeRules.iWidth σ) → Fin n) : data q t p ∘ position σ m d = p := by
  funext i; simp only [data, position, Function.comp_apply, Fin.append_right]

noncomputable def pattern (tm : FinTM2) (σ : Vocabulary) (m d w : Nat) :
    Fin (FactCodes.payloadWidth tm d w + 1) → Fin (MachineConstants.bound tm + numVars σ m d) :=
  InitialPatterns.configuration tm (Fin.castAdd _ (MachineConstants.numeral tm 0))
    (Fin.castAdd _ (MachineConstants.numeral tm 1))
    (Fin.castAdd _ (MachineConstants.control tm (.boundary (some tm.main))))
    (Fin.castAdd _ (MachineConstants.state tm tm.initialState))
    (Fin.natAdd _ ∘ time σ m d) (Fin.natAdd _ ∘ position σ m d)

noncomputable def rule (tm : FinTM2) (σ : Vocabulary) (m d w : Nat) :
    Template σ m (FactCodes.payloadWidth tm d w + 1) (MachineConstants.bound tm) where
  numVars := numVars σ m d
  guard := .conj (AddressFormulas.first (time σ m d))
    (InputLinkFormulas.first InputTupleCodes.arity_le_width (query σ m d) (position σ m d))
  guard_firstOrder := ⟨AddressFormulas.first_firstOrder _, InputLinkFormulas.first_firstOrder _ _ _⟩
  parameters := query σ m d
  head := pattern tm σ m d w
  premises := []

noncomputable def value {tm : FinTM2} {n iWidth d w : Nat} (hn : MachineConstants.bound tm ≤ n)
    (t : Fin d → Fin n) (p : Fin iWidth → Fin n) : Fin (FactCodes.payloadWidth tm d w + 1) → Fin n :=
  InitialPatterns.configuration tm ⟨0, by have := MachineConstants.enough tm; omega⟩
    ⟨1, by have := MachineConstants.enough tm; omega⟩
    (SupportedCodes.code _ ((MachineConstants.controls_bound tm).trans hn) (.boundary (some tm.main)))
    (@TupleCoding.finiteCode tm.σ tm.σFin n ((MachineConstants.states_bound tm).trans hn) tm.initialState) t p

theorem assignment_pattern {tm : FinTM2} {σ : Vocabulary} {m n d w : Nat}
    (hn : MachineConstants.bound tm ≤ n) (a : Fin (numVars σ m d) → Fin n) :
    assignment hn a ∘ pattern tm σ m d w = value (w := w) hn (a ∘ time σ m d) (a ∘ position σ m d) := by
  rw [pattern, InitialPatterns.map_configuration]
  have hd {k : Nat} (z : Fin k → Fin (numVars σ m d)) :
      assignment hn a ∘ (Fin.natAdd _ ∘ z) = a ∘ z := by funext i; simp [assignment]
  rw [hd, hd]
  simp only [assignment, Fin.append_left]
  rfl

def initial (tm : FinTM2) {Initial : Type} (p : Initial) : NodeMachine.Cfg tm.Γ tm.Λ tm.σ (TimedNodes.Node Initial) :=
  ⟨.boundary (some tm.main), tm.initialState, Function.update (fun _ => none) tm.k₀ (some (.inl p))⟩

theorem value_code {tm : FinTM2} {Initial : Type} {n iWidth d w : Nat}
    (P : FactCodes.Parameters tm Initial n iWidth d w) (hn : MachineConstants.bound tm ≤ n) (t : Nat) (p : Initial) :
    value (w := w) hn (TupleCoding.clock (d := d) (by have := P.enough; omega) t) (P.initial p) =
      FactCodes.code P (.config t (initial tm p)) := by
  unfold value InitialPatterns.configuration
  rw [InitialPatterns.initial_code P p, ← InitialPatterns.heads_none P,
    HeadPatterns.update_heads P (fun _ => none) tm.k₀ (some (.inl p))]
  rfl

end Lax751879Proofs.InitialConfigRules
