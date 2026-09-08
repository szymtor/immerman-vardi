import Lax979537Proofs.FixedPointEvaluation
import Lax979537Proofs.VardiImmerman
import Mathlib.Data.Fin.VecNotation

namespace VardiImmermanDecisionMachineTests

open Lax979537.OrderedStructures Lax979537.FixedPointSyntax Lax979537.StructureEncoding
open Lax979537Proofs Lax979537Proofs.StackProgram FormulaDecision Turing

def runFuel (tm : FinTM2) : Nat → tm.Cfg → tm.Cfg
  | 0, c => c
  | n + 1, c => match tm.step c with
      | none => c
      | some c' => runFuel tm n c'

def controlReset (s : FiniteDecoder.Control) : Bool := s == FiniteDecoder.initial
def eqBits (a b : List Bool) : Bool := a == b

/-- Start with mathlib's actual input configuration and inspect the exact
output convention: one bit, no other stack contents, reset finite control. -/
def check {σ : Vocabulary} {m : Nat} (φ : Formula σ m) (xs : List Bool) (fuel : Nat)
    (expected : Bool) : Bool :=
  let tm := machine (program φ) (inputPort φ) (inputPort φ) FiniteDecoder.initial
  let c := runFuel tm fuel (initList tm xs)
  c.l.isNone && controlReset c.var && (keys φ).all (fun key =>
    eqBits (c.stk key) (if key = inputPort φ then [expected] else []))

def disj {σ : Vocabulary} {m : Nat} {ρ : List Nat}
    (φ ψ : RawFormula σ m ρ) : RawFormula σ m ρ := .neg (.conj (.neg φ) (.neg ψ))

def reach : Formula [2] 2 :=
  ⟨.lfp 2 (disj (.equal 0 1) (.exists' (.conj (.relation 0 ![1, 0]) (.variable 0 ![0, 2])))) ![0, 1],
    by simp [disj, RawFormula.Admissible, RawFormula.positiveAt]⟩
def path : OrderedStructure [2] :=
  ⟨3, Fin.cons (fun t : Fin 2 → Fin 3 => decide ((t 0).val + 1 = (t 1).val)) (fun r => Fin.elim0 r)⟩
def forward : PointedStructure [2] 2 := ⟨path, (![0, 2] : Fin 2 → Fin 3)⟩
def backward : PointedStructure [2] 2 := ⟨path, (![2, 0] : Fin 2 → Fin 3)⟩
def diagonal : PointedStructure [2] 2 := ⟨path, (![1, 1] : Fin 2 → Fin 3)⟩

#guard check reach (encode forward) 1000000 true
#guard check reach (encode backward) 1000000 false
#guard check reach (encode diagonal) 1000000 true
#guard check reach (encode forward ++ [false]) 100000 false
#guard check reach ((encode forward).take 8) 100000 false
#guard check reach [] 100000 false

def truth : Formula [] 0 := ⟨.truth, trivial⟩
def nullary : Formula [0] 0 := ⟨.relation 0 Fin.elim0, trivial⟩
def emptyExists : Formula [] 0 := ⟨.exists' .truth, trivial⟩
def nullaryLfp : Formula [] 0 := ⟨.lfp 0 .truth Fin.elim0, by simp [RawFormula.Admissible, RawFormula.positiveAt]⟩
#guard check truth [false] 1000 true
#guard check emptyExists [false] 1000 false
#guard check nullaryLfp [false] 1000 true
#guard check nullary [false, true] 1000 true
#guard check nullary [false, false] 1000 false

def words : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (words n).flatMap fun xs => [false :: xs, true :: xs]

-- All short inputs exercise rejection and cleanup after partial parsing,
-- in addition to successful complete-machine runs.
#guard (List.range 6).all fun n => (words n).all fun xs =>
  check truth xs 10000 (DecisionProcedure.decideFormula truth xs) &&
    check nullary xs 10000 (DecisionProcedure.decideFormula nullary xs)

example {σ : Vocabulary} {m : Nat} (φ : Formula σ m) :
    Nonempty (TM2ComputableInPolyTime id (fun b => [b]) (DecisionProcedure.decideFormula φ)) :=
  computableInPolyTime φ

#print axioms Lax979537Proofs.FormulaDecision.computableInPolyTime
#print axioms Lax979537Proofs.FixedPointEvaluation.evaluationInP
#print axioms Lax979537Proofs.VardiImmerman.definable_inP
#print axioms Lax979537Proofs.VardiImmerman.capturesPtime

end VardiImmermanDecisionMachineTests
