import Lax751879Proofs.FactCodes
import Lax751879Proofs.SimulationHorizon

namespace Lax751879Proofs.TraceCodes

open Turing Lax751879.OrderedStructures
open InputSegments InputTupleCodes NodeClosure

noncomputable def threshold (tm : FinTM2) (σ : Vocabulary) (m : Nat) : Nat :=
  3 + tagBound σ m + ((TM2MicroSupport.controls tm).card + 1) +
    ((TM2Alphabet.alphabet tm).card + 1) + @Fintype.card tm.σ tm.σFin

@[reducible] def nodeWidth (σ : Vocabulary) (d : Nat) : Nat := max (width σ + 1) d
@[reducible] def arity (tm : FinTM2) (σ : Vocabulary) (d : Nat) : Nat :=
  FactCodes.payloadWidth tm d (nodeWidth σ d) + 1

noncomputable def parameters (tm : FinTM2) {σ : Vocabulary} {m : Nat}
    (d : Nat) (A : PointedStructure σ m) (hn : threshold tm σ m ≤ A.structureValue.size) :
    FactCodes.Parameters tm (Identifier σ m A.structureValue.size) A.structureValue.size
      (width σ + 1) d (nodeWidth σ d) where
  enough := by unfold threshold at hn; omega
  initial := InputTupleCodes.code (by unfold threshold at hn; omega) arity_le_width
  initial_injective := InputTupleCodes.code_injective _ _
  initial_width := Nat.le_max_left _ _
  clock_width := Nat.le_max_right _ _
  controls_bound := by unfold threshold at hn; omega
  symbols_bound := by unfold threshold at hn; omega
  states_bound := by unfold threshold at hn; omega

noncomputable def code (tm : FinTM2) {σ : Vocabulary} {m : Nat} (d : Nat)
    (A : PointedStructure σ m) (hn : threshold tm σ m ≤ A.structureValue.size)
    (f : Fact tm.Γ tm.Λ tm.σ (Identifier σ m A.structureValue.size)) :
    Fin (arity tm σ d) → Fin A.structureValue.size :=
  FactCodes.code (parameters tm d A hn) f

variable {f : List Bool → Bool}
  (h : TM2ComputableInPolyTime id (fun b : Bool => [b]) f)
  {σ : Vocabulary} {m : Nat} (d : Nat) (A : PointedStructure σ m)
  (hn : threshold h.tm σ m ≤ A.structureValue.size)

def encoded : Set (Fin (arity h.tm σ d) → Fin A.structureValue.size) :=
  code h.tm d A hn '' closure (SimulationHorizon.context h A) (A.structureValue.size ^ d - 1)

include hn in
theorem closure_valid (fact : Fact h.tm.Γ h.tm.Λ h.tm.σ (Identifier σ m A.structureValue.size))
    (hf : fact ∈ closure (SimulationHorizon.context h A) (A.structureValue.size ^ d - 1)) :
    FactSupport.Valid h.tm (A.structureValue.size ^ d) fact := by
  have hpos : 0 < A.structureValue.size := by unfold threshold at hn; omega
  have he : A.structureValue.size ^ d - 1 + 1 = A.structureValue.size ^ d :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.pow_pos hpos))
  have hv := FactSupport.closure_valid h.tm (InitialInput.raw h.tm h.inputAlphabet A)
    (InitialInput.names h.tm h.inputAlphabet A) (InitialInput.names_injective h.tm h.inputAlphabet A)
    (A.structureValue.size ^ d - 1) fact hf
  simpa only [he] using hv

/-- Decoding an encoded closure fact is unambiguous throughout the actual
bounded run, without an injectivity assumption on the unbounded raw type. -/
theorem code_injective_on_closure
    {p q : Fact h.tm.Γ h.tm.Λ h.tm.σ (Identifier σ m A.structureValue.size)}
    (hp : p ∈ closure (SimulationHorizon.context h A) (A.structureValue.size ^ d - 1))
    (hq : q ∈ closure (SimulationHorizon.context h A) (A.structureValue.size ^ d - 1))
    (he : code h.tm d A hn p = code h.tm d A hn q) : p = q :=
  FactCodes.code_injective (parameters h.tm d A hn)
    (closure_valid h d A hn p hp) (closure_valid h d A hn q hq) he

theorem mem_encoded_iff
    (p : Fact h.tm.Γ h.tm.Λ h.tm.σ (Identifier σ m A.structureValue.size))
    (hp : FactSupport.Valid h.tm (A.structureValue.size ^ d) p) :
    code h.tm d A hn p ∈ encoded h d A hn ↔
      p ∈ closure (SimulationHorizon.context h A) (A.structureValue.size ^ d - 1) := by
  constructor
  · rintro ⟨q, hq, he⟩
    have hqp := FactCodes.code_injective (parameters h.tm d A hn)
      (closure_valid h d A hn q hq) hp he
    exact hqp ▸ hq
  · intro hp; exact ⟨p, hp, rfl⟩

end Lax751879Proofs.TraceCodes
