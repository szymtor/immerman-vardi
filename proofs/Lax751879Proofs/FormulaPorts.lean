import Lax751879Proofs.FormulaProgram
import Lax751879Proofs.FiniteDecoder

namespace Lax751879Proofs.FormulaPorts

open Lax751879.OrderedStructures Lax751879.FixedPointSyntax FormulaProgram

/-- Explicit enumeration keeps the complete decision machine executable. -/
def workPorts {σ : Vocabulary} {m : Nat} {ρ : List Nat} :
    (φ : RawFormula σ m ρ) → List (Work φ)
  | .truth => []
  | .equal _ _ | .less _ _ | .relation _ _ | .variable _ _ => List.finRange 4
  | .neg φ => workPorts φ
  | .conj φ ψ => .saved :: ((workPorts φ).map .left ++ (workPorts ψ).map .right)
  | .exists' φ => [.counter, .coordinate, .tmp, .accumulator] ++ (workPorts φ).map .child
  | .lfp k body _ => [.tmp, .rev, .current, .nextTable, .bound, .counter, .stageCoordinate] ++
      (List.finRange k).map .power ++ (List.finRange k).map .tupleCounter ++
      (List.finRange k).map .tupleCoordinate ++ (workPorts body).map .child

theorem mem_workPorts {σ : Vocabulary} {m : Nat} {ρ : List Nat} (φ : RawFormula σ m ρ)
    (w : Work φ) : w ∈ workPorts φ := by
  induction φ with
  | truth => exact Empty.elim w
  | equal x y | less x y | relation r args | «variable» r args => simp [workPorts]
  | neg φ ih => exact ih w
  | conj φ ψ ihφ ihψ => cases w <;> simp [workPorts, ihφ, ihψ]
  | exists' φ ih => cases w <;> simp [workPorts, ih]
  | lfp k body args ih => cases w <;> simp [workPorts, ih]

def decoderPorts (σ : Vocabulary) (m : Nat) : List (FiniteDecoder.Port σ m) :=
  (List.finRange 5).map Sum.inl ++ (List.finRange σ.sum).map (FiniteDecoder.counterPort σ m) ++
    (List.finRange σ.length).map (FiniteDecoder.tablePort σ m) ++
    (List.finRange m).map (FiniteDecoder.coordPort σ m)

theorem mem_decoderPorts (σ : Vocabulary) (m : Nat) (p : FiniteDecoder.Port σ m) :
    p ∈ decoderPorts σ m := by
  rcases p with j | (j | (j | j)) <;>
    simp [decoderPorts, FiniteDecoder.counterPort, FiniteDecoder.tablePort, FiniteDecoder.coordPort]

end Lax751879Proofs.FormulaPorts
