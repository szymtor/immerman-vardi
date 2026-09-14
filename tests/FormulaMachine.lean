import Lax751879Proofs.FormulaLfpCorrectness
import Mathlib.Data.Fin.VecNotation

namespace ImmermanVardiFormulaMachineTests

open Lax751879.OrderedStructures Lax751879.FixedPointSyntax
open Lax751879Proofs Lax751879Proofs.StackProgram StackBoolean FormulaProgram Turing

def runFuel (tm : FinTM2) : Nat → tm.Cfg → tm.Cfg
  | 0, c => c
  | n + 1, c => match tm.step c with
      | none => c
      | some c' => runFuel tm n c'

abbrev Port {σ : Vocabulary} {m : Nat} (φ : RawFormula σ m []) :=
  (Fin 2 ⊕ (Fin m ⊕ Symbol σ)) ⊕ Work φ

def inputs {σ : Vocabulary} {m : Nat} (φ : RawFormula σ m []) : Inputs (Port φ) σ m [] :=
  ⟨.inl (.inl 0), fun i => .inl (.inr (.inl i)), fun r => .inl (.inr (.inr r)), Fin.elim0⟩

def initial {σ : Vocabulary} {m : Nat} (φ : RawFormula σ m []) (A : OrderedStructure σ)
    (v : Fin m → Fin A.size) : EvalStore (Port φ) Unit :=
  ⟨((((), false), true), some true), fun key => match key with
    | .inl (.inl j) => if j = 0 then List.replicate A.size true else [false, true, false]
    | .inl (.inr (.inl i)) => List.replicate (v i).val true
    | .inl (.inr (.inr r)) => (Lax751879.StructureEncoding.tuples A.size (σ.get r)).map (A.relation r)
    | .inr _ => []⟩

def stateEq (s : ((Unit × Bool) × Bool) × Option Bool) (b : Bool) : Bool :=
  s == ((((), true), b), none)

def stacksEq {K : Type} [Fintype K] (a b : K → List Bool) : Bool := decide (∀ key, a key = b key)

def check {σ : Vocabulary} {m : Nat} (φ : RawFormula σ m []) (A : OrderedStructure σ)
    (v : Fin m → Fin A.size) (fuel : Nat) (expected : Bool) : Bool :=
  let program : EvalProgram (Port φ) Unit := FormulaProgram.compile φ (inputs φ) Sum.inr
  let tm := machine program (.inl (.inl 0)) (.inl (.inl 1)) ((((), true), false), none)
  let s := initial φ A v
  let c := runFuel tm fuel (config (some (entry program)) s)
  c.l.isNone && stateEq c.var expected && stacksEq (K := Port φ) c.stk s.stk

def disj {σ : Vocabulary} {m : Nat} {ρ : List Nat}
    (φ ψ : RawFormula σ m ρ) : RawFormula σ m ρ := .neg (.conj (.neg φ) (.neg ψ))

def reach : RawFormula [2] 2 [] := .lfp 2
  (disj (.equal 0 1) (.exists' (.conj (.relation 0 ![1, 0]) (.variable 0 ![0, 2])))) ![0, 1]

def path : OrderedStructure [2] :=
  ⟨3, Fin.cons (fun t : Fin 2 → Fin 3 => decide ((t 0).val + 1 = (t 1).val)) (fun r => Fin.elim0 r)⟩

-- Actual TM2 execution of a compiled recursive reachability formula. The
-- current relation is read under an existential binder in each LFP round.
#guard check reach path (![0, 2] : Fin 2 → Fin 3) 1000000 true
#guard check reach path (![2, 0] : Fin 2 → Fin 3) 1000000 false
#guard check reach path (![1, 1] : Fin 2 → Fin 3) 1000000 true

-- An inner nullary LFP reads the outer unary relation through de Bruijn
-- relation index 1, while the outer body also reads a free element parameter.
def nested : RawFormula [2] 2 [] := .lfp 1
  (disj (.less 0 2) (.lfp 0 (.variable 1 ![0]) Fin.elim0)) ![0]
#guard check nested path (![0, 2] : Fin 2 → Fin 3) 100000 true
#guard check nested path (![2, 0] : Fin 2 → Fin 3) 100000 false

def emptyStructure : OrderedStructure [] := ⟨0, fun r => Fin.elim0 r⟩
#guard check (.truth : RawFormula [] 0 []) emptyStructure Fin.elim0 100 true
#guard check (.exists' .truth : RawFormula [] 0 []) emptyStructure Fin.elim0 100 false

-- Nullary LFP executes one round even on the empty universe.
#guard check (.lfp 0 .truth Fin.elim0 : RawFormula [] 0 []) emptyStructure Fin.elim0 1000 true
#guard check (.lfp 0 (.variable 0 Fin.elim0) Fin.elim0 : RawFormula [] 0 [])
  emptyStructure Fin.elim0 1000 false
#guard check (.lfp 0 (.lfp 0 .truth Fin.elim0) Fin.elim0 : RawFormula [] 0 [])
  emptyStructure Fin.elim0 10000 true

#guard [false, true].all fun b => check (.relation 0 Fin.elim0 : RawFormula [0] 0 [])
  ⟨0, fun _ _ => b⟩ Fin.elim0 100 b

-- Symbolic instantiation checks all domain sizes, states, and represented
-- inputs; the concrete examples above additionally exercise compiled code.
example {K Aux : Type} [DecidableEq K] : Correct (K := K) (Aux := Aux) reach :=
  compile_correct reach

#print axioms Lax751879Proofs.FormulaProgram.compile_correct
#print axioms Lax751879Proofs.FormulaProgram.correct_lfp
#print axioms Lax751879Proofs.TupleCoordinates.coordinate_ofFn

end ImmermanVardiFormulaMachineTests
