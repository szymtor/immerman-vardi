import Lax751879Proofs.FormulaLfpCorrectness
import Lax751879Proofs.FormulaPorts
import Lax751879Proofs.DecoderUnary
import Lax751879Proofs.StackRename
import Lax751879Proofs.StackOutput
import Lax751879Proofs.DecisionProcedure
import Lax751879Proofs.InputSize

namespace Lax751879Proofs.FormulaDecision

open Lax751879.OrderedStructures Lax751879.FixedPointSyntax
open StackProgram StackBoolean FormulaProgram

variable {σ : Vocabulary} {m : Nat}

abbrev Port (φ : Formula σ m) := FiniteDecoder.Port σ m ⊕ Work φ.val

def inputs (φ : Formula σ m) : Inputs (Port φ) σ m [] :=
  ⟨.inl (FiniteDecoder.work σ m).domain, fun i => .inl (FiniteDecoder.coordPort σ m i),
    fun r => .inl (FiniteDecoder.tablePort σ m r), fun r => Fin.elim0 r⟩

def inputPort (φ : Formula σ m) : Port φ := .inl (FiniteDecoder.work σ m).input

def keys (φ : Formula σ m) : List (Port φ) :=
  (FormulaPorts.decoderPorts σ m).map Sum.inl ++ (FormulaPorts.workPorts φ.val).map Sum.inr

theorem mem_keys (φ : Formula σ m) (key : Port φ) : key ∈ keys φ := by
  cases key <;> simp [keys, FormulaPorts.mem_decoderPorts, FormulaPorts.mem_workPorts]

def evaluate (φ : Formula σ m) : EvalProgram (Port φ) Unit :=
  .branch (fun s => s.1.2) (FormulaProgram.compile φ.val (inputs φ) Sum.inr) (answer false)

def program (φ : Formula σ m) : EvalProgram (Port φ) Unit :=
  .seq (StackRename.rename Sum.inl (FiniteDecoder.program σ m))
    (.seq (evaluate φ) (StackOutput.output (keys φ) (inputPort φ) FiniteDecoder.initial))

noncomputable def costPolynomial (φ : Formula σ m) : Polynomial Nat :=
  let D := StackDecoder.costPolynomial (FiniteDecoder.layout σ m)
  D + FormulaProgram.costPolynomial φ.val + 2 +
    (2 * (Polynomial.X + D) + 2) * Polynomial.C (keys φ).length + 3

def decoded (φ : Formula σ m) (xs : List Bool) : EvalStore (Port φ) Unit :=
  StackRename.sumStore
    (StackDecoder.result (FiniteDecoder.layout σ m) (FiniteDecoder.inputStore σ m xs)) (fun _ => [])

theorem decoded_represents (φ : Formula σ m) (xs : List Bool) (A : PointedStructure σ m)
    (hd : Decoding.decode σ m xs = some A) :
    Represents (inputs φ) A.structureValue A.tuple (fun r => Fin.elim0 r) (decoded φ xs) := by
  have hr := DecoderCorrectness.result_represents σ m xs A hd
  refine ⟨hr.ready.1, ?_, hr.tables, ?_⟩
  · intro i
    exact DecoderUnary.finite_coord σ m xs A hd i
  · intro r; exact Fin.elim0 r

theorem inputs_safe (φ : Formula σ m) : (inputs φ).Safe := by
  constructor
  · intro r; simp [inputs, FiniteDecoder.work, FiniteDecoder.tablePort]
  · intro r; exact Fin.elim0 r

theorem work_valid (φ : Formula σ m) : ValidWork (inputs φ) Sum.inr := by
  refine ⟨Sum.inr_injective, ?_⟩
  intro w
  refine ⟨by simp [inputs], ?_, ?_, ?_⟩
  · intro i; simp [inputs]
  · intro r; simp [inputs]
  · intro r; exact Fin.elim0 r

theorem evaluate_executes (φ : Formula σ m) (xs : List Bool) :
    ∃ c, c ≤ (FormulaProgram.costPolynomial φ.val).eval xs.length + 2 ∧
      Returns (evaluate φ) (decoded φ xs) (DecisionProcedure.decideFormula φ xs) c := by
  have hv := DecoderAgreement.finite_validity σ m xs
  cases hd : Decoding.decode σ m xs with
  | none =>
      have hf : (decoded φ xs).state.1.2 = false := by simpa [decoded, StackRename.sumStore, hd] using hv
      refine ⟨2, by omega, ?_⟩
      have hp := Executes.branch_false (b := fun s => s.1.2) (q := answer false)
        (p := FormulaProgram.compile φ.val (inputs φ) Sum.inr) hf (answer_returns false (decoded φ xs))
      simpa [evaluate, DecisionProcedure.decideFormula, DecisionProcedure.checkedDecode, hd] using hp
  | some A =>
      have he := DecoderSoundness.decode_sound σ m xs A hd
      have ht : (decoded φ xs).state.1.2 = true := by simpa [decoded, StackRename.sumStore, hd] using hv
      obtain ⟨c, hc, hp⟩ := FormulaProgram.compile_correct φ.val (inputs φ) Sum.inr
        (inputs_safe φ) (work_valid φ) A.structureValue A.tuple (fun r => Fin.elim0 r)
        (decoded φ xs) (fun _ => rfl) (decoded_represents φ xs A hd)
      have hn : A.structureValue.size ≤ xs.length := by
        have h := InputSize.domain_size_le_encoding A
        rw [he] at h
        omega
      have hb := PolynomialBounds.eval_mono (FormulaProgram.costPolynomial φ.val) hn
      refine ⟨c + 1, by omega, ?_⟩
      simpa [evaluate, DecisionProcedure.decideFormula, DecisionProcedure.checkedDecode, hd, he,
        DecisionProcedure.evaluatePointed] using Executes.branch_true (q := answer false) ht hp

/-- Complete execution on every bit string: decode, evaluate or reject,
clear all work, return one bit, and reset finite control. -/
theorem program_executes (φ : Formula σ m) (xs : List Bool) :
    ∃ c, c ≤ (costPolynomial φ).eval xs.length ∧
      Executes (program φ) (ioStore (inputPort φ) FiniteDecoder.initial xs)
        (ioStore (inputPort φ) FiniteDecoder.initial [DecisionProcedure.decideFormula φ xs]) c := by
  obtain ⟨d, hd, hp⟩ := FiniteDecoder.program_executes σ m xs
  have hdecode := StackRename.executes_in_sum hp (fun _ : Work φ.val => [])
  have hin : StackRename.sumStore (FiniteDecoder.inputStore σ m xs) (fun _ : Work φ.val => []) =
      ioStore (inputPort φ) FiniteDecoder.initial xs := by
    apply Store.ext
    · rfl
    · funext key
      cases key <;> simp [StackRename.sumStore, FiniteDecoder.inputStore, ioStore, inputPort]
  rw [hin] at hdecode
  change Executes (StackRename.rename Sum.inl (FiniteDecoder.program σ m))
    (ioStore (inputPort φ) FiniteDecoder.initial xs) (decoded φ xs) d at hdecode
  obtain ⟨e, he, heval⟩ := evaluate_executes φ xs
  let D := (StackDecoder.costPolynomial (FiniteDecoder.layout σ m)).eval xs.length
  have hspace (key : Port φ) : ((decoded φ xs).stk key).length ≤ xs.length + D := by
    have h := StackOutput.length_executes hdecode key
    have hi : ((ioStore (Γ := fun _ => Bool) (inputPort φ) FiniteDecoder.initial xs).stk key).length ≤ xs.length := by
      by_cases hk : key = inputPort φ
      · subst key; simp [ioStore]
      · simp [ioStore, hk]
    omega
  obtain ⟨o, ho, hout⟩ := StackOutput.output_executes (keys φ) (mem_keys φ) (inputPort φ) FiniteDecoder.initial
    (result (DecisionProcedure.decideFormula φ xs) (decoded φ xs)) (xs.length + D) hspace
  refine ⟨d + (e + o), ?_, Executes.seq hdecode (Executes.seq heval hout)⟩
  simp [costPolynomial]
  dsimp [D] at ho
  omega

theorem computableInPolyTime (φ : Formula σ m) :
    Nonempty (Turing.TM2ComputableInPolyTime id (fun b => [b]) (DecisionProcedure.decideFormula φ)) :=
  program_polytime (program φ) (inputPort φ) (inputPort φ) FiniteDecoder.initial id (fun b => [b])
    (DecisionProcedure.decideFormula φ) (costPolynomial φ) (program_executes φ)

end Lax751879Proofs.FormulaDecision
