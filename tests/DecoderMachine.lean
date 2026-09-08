import Lax979537Proofs.DecoderCorrectness

namespace ImmermanVardiDecoderTests

open Lax979537.OrderedStructures Lax979537.StructureEncoding
open Lax979537Proofs FiniteDecoder Turing

def runFuel (tm : FinTM2) : Nat → tm.Cfg → tm.Cfg
  | 0, c => c
  | n + 1, c => match tm.step c with
      | none => c
      | some c' => runFuel tm n c'

def eqBits (a b : List Bool) : Bool := a == b
def validity (s : Control) : Bool := s.1.2
def scratchClear (s : Control) : Bool := s.2.isNone

/-- Compare the concrete compiled machine with the independently defined
semantic decoder, including every retained table and pointed coordinate. -/
def checkDecoder (σ : Vocabulary) (k : Nat) (xs : List Bool) : Bool :=
  let tm := decoderMachine σ k
  let c := runFuel tm (cost σ k xs.length) (initList tm xs)
  let w := work σ k
  let clean := c.l.isNone && scratchClear c.var &&
    ([w.count, w.tmp, w.rev] ++ w.counters).all (fun p => eqBits (c.stk p) [])
  match Decoding.decode σ k xs with
  | none => clean && !validity c.var
  | some A => clean && validity c.var && eqBits (c.stk w.input) [] &&
      eqBits (c.stk w.domain) (List.replicate A.structureValue.size true) &&
      (List.finRange σ.length).all (fun r =>
        eqBits (c.stk (tablePort σ k r))
          ((tuples A.structureValue.size (σ.get r)).map (A.structureValue.relation r))) &&
      (List.finRange k).all (fun i =>
        eqBits (c.stk (coordPort σ k i)) (List.replicate (A.tuple i).val true))

def validMixed : List Bool :=
  unary 2 ++ [true, false, true, true, false, false, true] ++ unary 0 ++ unary 1

#guard checkDecoder [0, 1, 2] 2 validMixed
#guard checkDecoder [0, 1, 2] 2 (validMixed ++ [false])
#guard checkDecoder [0, 1, 2] 2 (validMixed.take (validMixed.length - 1))
#guard checkDecoder [0, 1, 2] 2 [true, true, false, true]
#guard checkDecoder [0] 0 [false, true]
#guard checkDecoder [0] 0 [false, false]
#guard checkDecoder [0] 0 [false]
#guard checkDecoder [] 0 [false]
#guard checkDecoder [] 1 [false, false]
#guard checkDecoder [] 0 []

def words : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (words n).flatMap (fun w => [false :: w, true :: w])

#guard (List.range 6).all (fun n => (words n).all (checkDecoder [0, 1] 1))
#guard (List.range 6).all (fun n => (words n).all (checkDecoder [2] 0))

#print axioms StackReadCoordinates.readCoords_executes
#print axioms StackDecoder.decode_executes
#print axioms FiniteDecoder.program_executes
#print axioms FiniteDecoder.decoder_runs
#print axioms DecoderSoundness.decode_sound
#print axioms DecoderSoundness.checkedDecode_eq_decode
#print axioms RawDecoding.decode_eq
#print axioms DecoderAgreement.tables_agree
#print axioms DecoderAgreement.coords_agree
#print axioms DecoderAgreement.decode_agree
#print axioms DecoderAgreement.finite_agree
#print axioms DecoderAgreement.accepts_iff_encoding
#print axioms DecoderCorrectness.result_represents
#print axioms DecoderCorrectness.decoder_correct

end ImmermanVardiDecoderTests
