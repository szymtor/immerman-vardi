import Lax751879Proofs.StackAtomic
import Lax751879Proofs.StackExists
import Lax751879Proofs.StackLfpArity
import Mathlib.Tactic.DeriveFintype

namespace Lax751879Proofs.FormulaProgram

open Lax751879.OrderedStructures Lax751879.FixedPointSyntax StackBoolean

inductive BinaryWork (Left Right : Type)
  | saved
  | left (port : Left)
  | right (port : Right)
  deriving DecidableEq, Fintype

inductive ExistsWork (Child : Type)
  | counter | coordinate | tmp | accumulator
  | child (port : Child)
  deriving DecidableEq, Fintype

inductive LfpWork (k : Nat) (Child : Type)
  | tmp | rev | current | nextTable | bound | counter | stageCoordinate
  | power (i : Fin k)
  | tupleCounter (i : Fin k)
  | tupleCoordinate (i : Fin k)
  | child (port : Child)
  deriving DecidableEq, Fintype

/-- Private stack ports determined entirely by the formula syntax. -/
@[reducible] def Work {σ : Vocabulary} {m : Nat} {ρ : List Nat} : RawFormula σ m ρ → Type
  | .truth => Empty
  | .equal _ _ | .less _ _ | .relation _ _ | .variable _ _ => Fin 4
  | .neg φ => Work φ
  | .conj φ ψ => BinaryWork (Work φ) (Work ψ)
  | .exists' φ => ExistsWork (Work φ)
  | .lfp k body _ => LfpWork k (Work body)

@[reducible] def workFintype {σ : Vocabulary} {m : Nat} {ρ : List Nat} :
    (φ : RawFormula σ m ρ) → Fintype (Work φ)
  | .truth => inferInstance
  | .equal _ _ | .less _ _ | .relation _ _ | .variable _ _ => inferInstance
  | .neg φ => workFintype φ
  | .conj φ ψ => letI := workFintype φ; letI := workFintype ψ; inferInstance
  | .exists' φ => letI := workFintype φ; inferInstance
  | .lfp _ body _ => letI := workFintype body; inferInstance

@[reducible] def workDecidableEq {σ : Vocabulary} {m : Nat} {ρ : List Nat} :
    (φ : RawFormula σ m ρ) → DecidableEq (Work φ)
  | .truth => inferInstance
  | .equal _ _ | .less _ _ | .relation _ _ | .variable _ _ => inferInstance
  | .neg φ => workDecidableEq φ
  | .conj φ ψ => letI := workDecidableEq φ; letI := workDecidableEq ψ; inferInstance
  | .exists' φ => letI := workDecidableEq φ; inferInstance
  | .lfp _ body _ => letI := workDecidableEq body; inferInstance

instance {σ : Vocabulary} {m : Nat} {ρ : List Nat} (φ : RawFormula σ m ρ) : Fintype (Work φ) := workFintype φ
instance {σ : Vocabulary} {m : Nat} {ρ : List Nat} (φ : RawFormula σ m ρ) : DecidableEq (Work φ) := workDecidableEq φ

structure Inputs (K : Type) (σ : Vocabulary) (m : Nat) (ρ : List Nat) where
  domain : K
  element : Fin m → K
  symbol : Symbol σ → K
  relation : Fin ρ.length → K

def Inputs.existsPorts {K : Type} {σ : Vocabulary} {m : Nat} {ρ : List Nat}
    (input : Inputs K σ m ρ) (coordinate : K) : Inputs K σ (m + 1) ρ :=
  ⟨input.domain, Fin.cons coordinate input.element, input.symbol, input.relation⟩

def Inputs.lfpPorts {K : Type} {σ : Vocabulary} {m k : Nat} {ρ : List Nat}
    (input : Inputs K σ m ρ) (coordinates : Fin k → K) (current : K) : Inputs K σ (k + m) (k :: ρ) :=
  ⟨input.domain, Fin.append coordinates input.element, input.symbol, Fin.cons current input.relation⟩

/-- A fixed stack program for every raw formula. Inputs, private-port maps,
and syntax are its only parameters; structures and domain sizes are absent. -/
def compile {K Aux : Type} [DecidableEq K] {σ : Vocabulary} {m : Nat} {ρ : List Nat} :
    (φ : RawFormula σ m ρ) → Inputs K σ m ρ → (Work φ → K) → EvalProgram K Aux
  | .truth, _, _ => answer true
  | .equal x y, input, work => StackAtomic.equalValue (input.element x) (input.element y)
      (work 0) (work 1) (work 2) (work 3)
  | .less x y, input, work => StackAtomic.lessValue (input.element x) (input.element y)
      (work 0) (work 1) (work 2)
  | .relation r args, input, work => StackTableLookup.lookup input.domain (input.symbol r)
      (work 0) (work 1) (work 2) (work 3) (List.ofFn (input.element ∘ args))
  | .variable r args, input, work => StackTableLookup.lookup input.domain (input.relation r)
      (work 0) (work 1) (work 2) (work 3) (List.ofFn (input.element ∘ args))
  | .neg φ, input, work => .seq (compile φ input work) negate
  | .conj φ ψ, input, work => binary (work .saved) (· && ·)
      (compile φ input (fun p => work (.left p))) (compile ψ input (fun p => work (.right p)))
  | .exists' φ, input, work => StackExists.existsValues input.domain (work .counter) (work .coordinate)
      (work .tmp) (work .accumulator)
      (compile φ (input.existsPorts (work .coordinate)) (fun p => work (.child p)))
  | .lfp _ body args, input, work => StackLfpValue.evaluate input.domain
      (work .tmp) (work .rev) (work .current) (work .nextTable) (work .bound) (work .counter) (work .stageCoordinate)
      (List.ofFn (fun i => work (.power i)))
      (List.ofFn (fun i => (work (.tupleCounter i), work (.tupleCoordinate i))))
      (List.ofFn (input.element ∘ args))
      (compile body (input.lfpPorts (fun i => work (.tupleCoordinate i)) (work .current)) (fun p => work (.child p)))

noncomputable def costPolynomial {σ : Vocabulary} {m : Nat} {ρ : List Nat} :
    RawFormula σ m ρ → Polynomial Nat
  | .truth => 1
  | .equal _ _ | .less _ _ => 48 * Polynomial.X + 41
  | .relation r _ => StackTableLookup.costPolynomial (σ.get r)
  | .variable r _ => StackTableLookup.costPolynomial (ρ.get r)
  | .neg φ => costPolynomial φ + 1
  | .conj φ ψ => costPolynomial φ + costPolynomial ψ + 2
  | .exists' φ => (costPolynomial φ + 15) * Polynomial.X + 11
  | .lfp k body _ => StackLfpValue.costPolynomial (costPolynomial body) k

end Lax751879Proofs.FormulaProgram
