import Lax751879Proofs.DecoderCorrectness

namespace Lax751879Proofs.DecoderUnary

open Lax751879.OrderedStructures StackProgram StackTransfer StackReadRelations

variable {K Aux : Type} [DecidableEq K]

theorem coordinate_unary (input coord domain key : K) (hi : key ≠ input)
    (s : BitStore K ((Aux × Bool) × Bool)) (hs : ∃ n, s.stk key = List.replicate n true) :
    ∃ n, (StackCoordinate.result input coord domain s).stk key = List.replicate n true := by
  obtain ⟨n, hn⟩ := hs
  by_cases he : key = coord
  · subst key
    refine ⟨(StackUnary.splitUnary (s.stk input)).1 + n, ?_⟩
    simp [StackCoordinate.result, StackCheckBound.result, StackCheckedUnary.result, hn]
  · exact ⟨n, (StackCoordinate.result_preserves input coord domain key hi he s).trans hn⟩

theorem coords_unary (w : Workspace K) (coords : List K) (key : K) (hi : key ≠ w.input)
    (s : BitStore K ((Aux × Bool) × Bool)) (hs : ∃ n, s.stk key = List.replicate n true) :
    ∃ n, (StackReadCoordinates.result w coords s).stk key = List.replicate n true := by
  induction coords generalizing s with
  | nil => exact hs
  | cons c cs ih => exact ih _ (coordinate_unary w.input c w.domain key hi s hs)

theorem result_coord_unary (l : StackDecoder.Layout K) (s : BitStore K ((Aux × Bool) × Bool))
    (key : K) (hk : key ∈ l.coords) (hs : s.stk key = []) :
    ∃ n, (StackDecoder.result l s).stk key = List.replicate n true := by
  have hf := (l.coord_fresh key hk).1
  have hi : key ≠ l.work.input := by
    simp only [List.mem_cons, List.not_mem_nil, not_false_eq_true, not_or, and_true] at hf
    exact hf.2.1
  have hd : key ≠ l.work.domain := by
    simp only [List.mem_cons, List.not_mem_nil, not_false_eq_true, not_or, and_true] at hf
    exact hf.1
  apply coords_unary l.work l.coords key hi
  refine ⟨0, ?_⟩
  rw [StackReadRelations.result_preserves l.work _ l.tables key hi (l.disjoint key hk),
    StackCheckedUnary.result_preserves l.work.input l.work.domain key hi hd, hs]
  rfl

theorem finite_coord (σ : Vocabulary) (k : Nat) (xs : List Bool) (A : PointedStructure σ k)
    (hd : Decoding.decode σ k xs = some A) (i : Fin k) :
    (StackDecoder.result (FiniteDecoder.layout σ k) (FiniteDecoder.inputStore σ k xs)).stk
      (FiniteDecoder.coordPort σ k i) = List.replicate (A.tuple i).val true := by
  obtain ⟨n, hn⟩ := result_coord_unary (FiniteDecoder.layout σ k) (FiniteDecoder.inputStore σ k xs)
    (FiniteDecoder.coordPort σ k i) (by simp [FiniteDecoder.layout, FiniteDecoder.coords])
    (by simp [FiniteDecoder.inputStore, ioStore, FiniteDecoder.coordPort, FiniteDecoder.work])
  have hl := (DecoderCorrectness.result_represents σ k xs A hd).coords i
  rw [hn, List.length_replicate] at hl
  simpa only [hl] using hn

end Lax751879Proofs.DecoderUnary
