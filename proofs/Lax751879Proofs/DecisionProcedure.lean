import Lax751879Proofs.Decoding
import Lax751879Proofs.TableEvaluation
import Lax751879.PolynomialTime

namespace Lax751879Proofs.DecisionProcedure

open Lax751879.OrderedStructures Lax751879.FixedPointSyntax
open Lax751879.FixedPointSemantics Lax751879.StructureEncoding
open Lax751879.PolynomialTime
open Lax751879Proofs.Decoding Lax751879Proofs.TableEvaluation

/-- A final serialization check makes rejection of every noncanonical input
explicit. Both parsing and this check operate on the supplied bit string. -/
def checkedDecode (σ : Vocabulary) (k : Nat) (w : List Bool) :
    Option (PointedStructure σ k) :=
  match decode σ k w with
  | none => none
  | some A => if encode A = w then some A else none

theorem checkedDecode_encode {σ : Vocabulary} {k : Nat} (A : PointedStructure σ k) :
    checkedDecode σ k (encode A) = some A := by
  simp [checkedDecode, decode_encode]

theorem checkedDecode_sound {σ : Vocabulary} {k : Nat} {w : List Bool}
    {A : PointedStructure σ k} (h : checkedDecode σ k w = some A) : encode A = w := by
  cases hd : decode σ k w with
  | none => simp [checkedDecode, hd] at h
  | some B =>
      by_cases he : encode B = w
      · have hBA : B = A := by simpa [checkedDecode, hd, he] using h
        exact hBA ▸ he
      · simp [checkedDecode, hd, he] at h

def evaluatePointed {σ : Vocabulary} {k : Nat} (φ : Formula σ k)
    (A : PointedStructure σ k) : Bool :=
  evaluate φ.val A.structureValue A.tuple (fun r => Fin.elim0 r)

theorem evaluatePointed_correct {σ : Vocabulary} {k : Nat} (φ : Formula σ k)
    (A : PointedStructure σ k) : evaluatePointed φ A = true ↔ Satisfies A φ := by
  have he : denote (n := A.structureValue.size) (ρ := []) (fun r => Fin.elim0 r) =
      (fun r => Fin.elim0 r) := by
    funext r
    exact Fin.elim0 r
  simpa only [evaluatePointed, Satisfies, he] using
    evaluate_correct φ.val φ.property A.structureValue A.tuple (fun r => Fin.elim0 r)

/-- Total executable decision function on bit strings. The separate machine
compiler and its polynomial step bound are still needed for `evaluationInP`. -/
def decideFormula {σ : Vocabulary} {k : Nat} (φ : Formula σ k) (w : List Bool) : Bool :=
  match checkedDecode σ k w with
  | none => false
  | some A => evaluatePointed φ A

theorem decideFormula_correct {σ : Vocabulary} {k : Nat} (φ : Formula σ k)
    (w : List Bool) :
    decideFormula φ w = true ↔ language (fun A => Satisfies A φ) w := by
  constructor
  · intro h
    cases hd : checkedDecode σ k w with
    | none => simp [decideFormula, hd] at h
    | some A =>
        refine ⟨A, checkedDecode_sound hd, ?_⟩
        apply (evaluatePointed_correct φ A).mp
        simpa [decideFormula, hd] using h
  · rintro ⟨A, rfl, hA⟩
    simpa only [decideFormula, checkedDecode_encode] using
      (evaluatePointed_correct φ A).mpr hA

end Lax751879Proofs.DecisionProcedure
