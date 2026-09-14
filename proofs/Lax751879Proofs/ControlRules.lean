import Lax751879Proofs.FactPatterns
import Lax751879Proofs.MachineConstants

namespace Lax751879Proofs.ControlRules

open Turing Lax751879.OrderedStructures Lax751879.FixedPointSyntax
open Lax751879.FixedPointSemantics
open RuleConstants FactPatterns

variable {σ : Vocabulary} {m d H n : Nat}

def query (m d H : Nat) : Fin m → Fin (m + (d + (d + H))) := Fin.castAdd _
def before (m d H : Nat) : Fin d → Fin (m + (d + (d + H))) := Fin.natAdd m ∘ Fin.castAdd _
def after (m d H : Nat) : Fin d → Fin (m + (d + (d + H))) :=
  Fin.natAdd m ∘ Fin.natAdd d ∘ Fin.castAdd H
def heads (m d H : Nat) : Fin H → Fin (m + (d + (d + H))) :=
  Fin.natAdd m ∘ Fin.natAdd d ∘ Fin.natAdd d

def data (q : Fin m → Fin n) (x y : Fin d → Fin n) (h : Fin H → Fin n) :
    Fin (m + (d + (d + H))) → Fin n := Fin.append q (Fin.append x (Fin.append y h))

@[simp] theorem data_query (q : Fin m → Fin n) (x y : Fin d → Fin n) (h : Fin H → Fin n) :
    data q x y h ∘ query m d H = q := by funext i; simp [data, query]
@[simp] theorem data_before (q : Fin m → Fin n) (x y : Fin d → Fin n) (h : Fin H → Fin n) :
    data q x y h ∘ before m d H = x := by funext i; simp [data, before]
@[simp] theorem data_after (q : Fin m → Fin n) (x y : Fin d → Fin n) (h : Fin H → Fin n) :
    data q x y h ∘ after m d H = y := by funext i; simp [data, after]
@[simp] theorem data_heads (q : Fin m → Fin n) (x y : Fin d → Fin n) (h : Fin H → Fin n) :
    data q x y h ∘ heads m d H = h := by funext i; simp [data, heads]

variable (tm : FinTM2) (m d w : Nat)

@[reducible] def headWidth : Nat := FactCodes.stackCount tm * (w + 1)
@[reducible] def numVars : Nat := m + (d + (d + headWidth tm w))

/-- A configuration pattern at one of the two clock blocks. The cursor and
state are fixed machine constants; stack heads are shared data variables. -/
noncomputable def pattern (c : TM2Micro.Cursor tm.Γ tm.Λ tm.σ) (v : tm.σ)
    (time : Fin d → Fin (numVars tm m d w)) :
    Fin (FactCodes.payloadWidth tm d w + 1) → Fin (MachineConstants.bound tm + numVars tm m d w) :=
  configuration tm
    (Fin.castAdd _ (MachineConstants.numeral tm 0))
    (Fin.castAdd _ (MachineConstants.numeral tm 0))
    (Fin.natAdd _ ∘ time)
    (Fin.castAdd _ (MachineConstants.control tm c))
    (Fin.castAdd _ (MachineConstants.state tm v))
    (Fin.natAdd _ ∘ heads m d (headWidth tm w))

/-- One positive rule advances the clock and changes fixed control/state
constants while preserving every stack head. -/
noncomputable def transition (c c' : TM2Micro.Cursor tm.Γ tm.Λ tm.σ) (v v' : tm.σ) :
    Template σ m (FactCodes.payloadWidth tm d w + 1) (MachineConstants.bound tm) where
  numVars := numVars tm m d w
  guard := AddressFormulas.successor (before m d (headWidth tm w)) (after m d (headWidth tm w))
  guard_firstOrder := AddressFormulas.successor_firstOrder _ _
  parameters := query m d (headWidth tm w)
  head := pattern tm m d w c' v' (after m d (headWidth tm w))
  premises := [pattern tm m d w c v (before m d (headWidth tm w))]

variable {tm m d w}

noncomputable def value {n : Nat} (hn : MachineConstants.bound tm ≤ n)
    (c : TM2Micro.Cursor tm.Γ tm.Λ tm.σ) (v : tm.σ)
    (time : Fin d → Fin n) (h : Fin (headWidth tm w) → Fin n) :
    Fin (FactCodes.payloadWidth tm d w + 1) → Fin n :=
  configuration tm ⟨0, by have := MachineConstants.enough tm; omega⟩
    ⟨0, by have := MachineConstants.enough tm; omega⟩ time
    (SupportedCodes.code _ ((MachineConstants.controls_bound tm).trans hn) c)
    (@TupleCoding.finiteCode tm.σ tm.σFin n ((MachineConstants.states_bound tm).trans hn) v) h

theorem assignment_pattern {n : Nat} (hn : MachineConstants.bound tm ≤ n)
    (a : Fin (numVars tm m d w) → Fin n)
    (c : TM2Micro.Cursor tm.Γ tm.Λ tm.σ) (v : tm.σ)
    (time : Fin d → Fin (numVars tm m d w)) :
    assignment hn a ∘ pattern tm m d w c v time =
      value hn c v (a ∘ time) (a ∘ heads m d (headWidth tm w)) := by
  rw [pattern, map_configuration]
  have hdata (z : Fin d → Fin (numVars tm m d w)) :
      assignment hn a ∘ (Fin.natAdd _ ∘ z) = a ∘ z := by funext i; simp [assignment]
  have hheads : assignment hn a ∘ (Fin.natAdd _ ∘ heads m d (headWidth tm w)) =
      a ∘ heads m d (headWidth tm w) := by funext i; simp [assignment]
  rw [hdata, hheads]
  simp only [assignment, Fin.append_left]
  rfl

/-- Exact interpretation of the compiled rule. The witness heads can be any
tuple; when the premise belongs to the encoded trace, its support and
decoding invariants supply their machine interpretation. -/
theorem transition_holds (c c' : TM2Micro.Cursor tm.Γ tm.Λ tm.σ) (v v' : tm.σ)
    (A : OrderedStructure σ) (hn : MachineConstants.bound tm ≤ A.size)
    (q : Fin m → Fin A.size) (R : Set (Fin (FactCodes.payloadWidth tm d w + 1) → Fin A.size))
    (out : Fin (FactCodes.payloadWidth tm d w + 1) → Fin A.size) :
    (compile (transition tm m d w c c' v v')).holds A q R out ↔
      ∃ x y : Fin d → Fin A.size, ∃ h : Fin (headWidth tm w) → Fin A.size,
        (TupleAddresses.address A.size d x).val + 1 = (TupleAddresses.address A.size d y).val ∧
        value hn c' v' y h = out ∧ value hn c v x h ∈ R := by
  rw [compile_holds _ A hn]
  dsimp only [holds, transition]
  constructor
  · rintro ⟨a, hg, _, he, hp⟩
    refine ⟨a ∘ before m d (headWidth tm w), a ∘ after m d (headWidth tm w),
      a ∘ heads m d (headWidth tm w), ?_, ?_, ?_⟩
    · exact (AddressFormulas.eval_successor _ _ _ _ _).mp hg
    · exact (assignment_pattern hn a c' v' _).symm.trans he
    · have h := hp _ (List.mem_singleton_self _)
      rw [assignment_pattern hn a c v (before m d (headWidth tm w))] at h
      exact h
  · rintro ⟨x, y, h, hs, he, hp⟩
    refine ⟨data q x y h, ?_, data_query q x y h, ?_, ?_⟩
    · apply (AddressFormulas.eval_successor _ _ _ _ _).mpr
      simpa only [data_before q x y h, data_after q x y h] using hs
    · simpa only [transition, assignment_pattern, data_after, data_heads] using he
    · intro b hb
      have hb' : b = pattern tm m d w c v (before m d (headWidth tm w)) := List.mem_singleton.mp hb
      subst b
      rw [assignment_pattern hn (data q x y h) c v (before m d (headWidth tm w)),
        data_before q x y h, data_heads q x y h]
      exact hp

end Lax751879Proofs.ControlRules
