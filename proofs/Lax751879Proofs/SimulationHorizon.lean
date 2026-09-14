import Lax751879Proofs.InitialInput
import Lax751879Proofs.NodeAcceptance
import Lax751879Proofs.InputSize
import Lax751879Proofs.PolynomialBounds

namespace Lax751879Proofs.SimulationHorizon

open Turing Lax751879.OrderedStructures Lax751879.StructureEncoding
open Polynomial

/-- Only a polynomial bound is needed: one tuple dimension absorbs input
encoding length, the given running-time polynomial, and microstep overhead. -/
theorem exists_horizon (σ : Vocabulary) (m : Nat) (tm : FinTM2) (time : Polynomial Nat) :
    ∃ d : Nat, ∀ A : PointedStructure σ m, 2 ≤ A.structureValue.size →
      TM2Micro.factor tm * time.eval (encode A).length ≤ A.structureValue.size ^ d - 1 := by
  obtain ⟨d, hd⟩ := PolynomialBounds.exists_power
    (C (TM2Micro.factor tm) * time.comp (InputSize.encodingPolynomial σ m))
  refine ⟨d, fun A hA => ?_⟩
  have hm := Nat.mul_le_mul_left (TM2Micro.factor tm)
    (PolynomialBounds.eval_mono time (InputSize.encoding_length_le A))
  have hb := hd A.structureValue.size hA
  simp only [eval_mul, eval_C, eval_comp] at hb
  omega

variable {f : List Bool → Bool}
  (h : TM2ComputableInPolyTime id (fun b : Bool => [b]) f)
  {σ : Vocabulary} {m : Nat} (A : PointedStructure σ m)

noncomputable def context :=
  NodeTrace.input h.tm (InitialInput.raw h.tm h.inputAlphabet A)
    (InitialInput.names h.tm h.inputAlphabet A) (InitialInput.names_injective h.tm h.inputAlphabet A)

def accepts (d : Nat) (b : Bool) : Prop :=
  NodeAcceptance.accepts
    (NodeClosure.closure (context h A) (A.structureValue.size ^ d - 1))
    (A.structureValue.size ^ d - 1) h.tm.k₁ (h.outputAlphabet.symm b)

/-- The concrete positive computation closure decides each encoded pointed
structure at a sufficiently large tuple-clock horizon. FO rule presentation
is still a separate obligation. -/
theorem accepts_iff (d : Nat) (b : Bool)
    (hN : TM2Micro.factor h.tm * h.time.eval (encode A).length ≤ A.structureValue.size ^ d - 1) :
    accepts h A d b ↔ b = f (encode A) := by
  have hr : StateTransition.EvalsToInTime h.tm.step
      (initList h.tm (InitialInput.raw h.tm h.inputAlphabet A))
      (some (haltList h.tm [h.outputAlphabet.symm (f (encode A))]))
      (h.time.eval (encode A).length) := by
    simpa only [TM2OutputsInTime, id_eq, List.map_cons, List.map_nil, Option.map_some,
      InitialInput.raw_eq_encode] using h.outputsFun (encode A)
  exact (NodeAcceptance.accepts_iff h.tm (InitialInput.raw h.tm h.inputAlphabet A)
    (InitialInput.names h.tm h.inputAlphabet A) (InitialInput.names_injective h.tm h.inputAlphabet A)
    (h.outputAlphabet.symm (f (encode A))) (h.outputAlphabet.symm b) hr hN).trans
      h.outputAlphabet.symm.injective.eq_iff

theorem exists_deciding_horizon (σ : Vocabulary) (m : Nat) :
    ∃ d : Nat, ∀ A : PointedStructure σ m, 2 ≤ A.structureValue.size →
      ∀ b : Bool, accepts h A d b ↔ b = f (encode A) := by
  obtain ⟨d, hd⟩ := exists_horizon σ m h.tm h.time
  exact ⟨d, fun A hA b => accepts_iff h A d b (hd A hA)⟩

end Lax751879Proofs.SimulationHorizon
