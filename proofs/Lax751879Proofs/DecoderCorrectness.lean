import Lax751879Proofs.DecoderAgreement

namespace Lax751879Proofs.DecoderCorrectness

open Lax751879.OrderedStructures Lax751879.StructureEncoding
open StackProgram StackTransfer StackReadRelations FiniteDecoder

/-- Input representation supplied to the formula evaluator: a unary domain
counter, canonical dense relation tables, bounded coordinate counters, and
an empty reusable decoder workspace. -/
structure Represents {σ : Vocabulary} {k : Nat} (A : PointedStructure σ k)
    (s : BitStore (Port σ k) ((Unit × Bool) × Bool)) : Prop where
  ready : Ready (work σ k) A.structureValue.size s
  input_empty : s.stk (work σ k).input = []
  tables : ∀ r : Symbol σ, s.stk (tablePort σ k r) =
    (tuples A.structureValue.size (σ.get r)).map (A.structureValue.relation r)
  coords : ∀ i : Fin k, (s.stk (coordPort σ k i)).length = (A.tuple i).val

theorem result_input_empty (σ : Vocabulary) (k : Nat) (xs : List Bool)
    (h : (StackDecoder.result (layout σ k) (inputStore σ k xs)).state.1.2 = true) :
    (StackDecoder.result (layout σ k) (inputStore σ k xs)).stk (work σ k).input = [] := by
  simp only [StackDecoder.result, StackDecoder.finish, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

theorem result_represents (σ : Vocabulary) (k : Nat) (xs : List Bool) (A : PointedStructure σ k)
    (hd : Decoding.decode σ k xs = some A) :
    Represents A (StackDecoder.result (layout σ k) (inputStore σ k xs)) := by
  let t := StackDecoder.result (layout σ k) (inputStore σ k xs)
  have hr := StackDecoder.result_ready (layout σ k) (inputStore σ k xs)
    (fun p hp => by
      change p ≠ (work σ k).input at hp
      simp [inputStore, ioStore, hp])
  have hdata := DecoderAgreement.finite_data σ k xs A hd
  have hsize := congrArg RawDecoding.Data.size hdata
  change (t.stk (work σ k).domain).length = A.structureValue.size at hsize
  have hlen := congrArg List.length hr.1
  simp only [List.length_replicate] at hlen
  have hn : (StackUnary.splitUnary ((inputStore σ k xs).stk (layout σ k).work.input)).1 =
      A.structureValue.size := hlen.symm.trans hsize
  rw [hn] at hr
  have hv : t.state.1.2 = true := by
    simpa [hd] using DecoderAgreement.finite_validity σ k xs
  refine ⟨hr, result_input_empty σ k xs hv, ?_, ?_⟩
  · have ht := congrArg RawDecoding.Data.tables hdata
    change DecoderAgreement.tableData (layout σ k).tables t =
      RawDecoding.tableView A.structureValue.size A.structureValue.relation at ht
    simp only [DecoderAgreement.tableData, layout, FiniteDecoder.tables, RawDecoding.tableView,
      List.map_map, Function.comp_def] at ht
    intro r
    exact List.map_inj_left.mp ht r (by simp)
  · have hc := congrArg RawDecoding.Data.coords hdata
    change DecoderAgreement.coordData (layout σ k).coords t = RawDecoding.coordView A.tuple at hc
    simp only [DecoderAgreement.coordData, layout, FiniteDecoder.coords, RawDecoding.coordView,
      List.map_map, Function.comp_def] at hc
    intro i
    exact List.map_inj_left.mp hc i (by simp)

/-- End-to-end concrete decoder theorem: bounded actual TM2 execution,
exact recognition of canonical encodings, and the representation required
by the evaluator whenever the input encodes a pointed ordered structure. -/
theorem decoder_correct (σ : Vocabulary) (k : Nat) (xs : List Bool) :
    ∃ (t : Nat) (s : BitStore (Port σ k) ((Unit × Bool) × Bool)),
      t ≤ cost σ k xs.length ∧
      Nonempty (StateTransition.EvalsToInTime (decoderMachine σ k).step
        (Turing.initList (decoderMachine σ k) xs) (some (config none s)) t) ∧
      (s.state.1.2 = true ↔ ∃ A : PointedStructure σ k, encode A = xs) ∧
      (∀ A : PointedStructure σ k, encode A = xs → Represents A s) := by
  obtain ⟨t, ht, hr⟩ := decoder_runs σ k xs
  refine ⟨t, StackDecoder.result (layout σ k) (inputStore σ k xs), ht, hr,
    DecoderAgreement.accepts_iff_encoding σ k xs, ?_⟩
  intro A he
  apply result_represents σ k xs A
  rw [← he, Decoding.decode_encode]

end Lax751879Proofs.DecoderCorrectness
