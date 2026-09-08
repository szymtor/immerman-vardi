import Lax979537Proofs.DecisionProcedure
import Mathlib.Data.Fin.VecNotation

open Lax979537.OrderedStructures Lax979537.FixedPointSyntax
open Lax979537.StructureEncoding Lax979537Proofs.DecisionProcedure

namespace VardiImmermanTests

def disj {σ : Vocabulary} {m : Nat} {ρ : List Nat}
    (φ ψ : RawFormula σ m ρ) : RawFormula σ m ρ :=
  .neg (.conj (.neg φ) (.neg ψ))

/-- Reflexive directed reachability, with two free element variables. -/
def reach : Formula [2] 2 :=
  ⟨.lfp 2
    (disj (.equal 0 1)
      (.exists' (.conj (.relation 0 ![1, 0]) (.variable 0 ![0, 2]))))
    ![0, 1], by simp [disj, RawFormula.Admissible, RawFormula.positiveAt]⟩

def path : OrderedStructure [2] where
  size := 3
  relation := Fin.cons (fun t : Fin 2 → Fin 3 => decide ((t 0).val + 1 = (t 1).val))
    (fun r => Fin.elim0 r)

def forward : PointedStructure [2] 2 := ⟨path, (![0, 2] : Fin 2 → Fin 3)⟩
def backward : PointedStructure [2] 2 := ⟨path, (![2, 0] : Fin 2 → Fin 3)⟩
def diagonal : PointedStructure [2] 2 := ⟨path, (![1, 1] : Fin 2 → Fin 3)⟩

#guard decideFormula reach (encode forward)
#guard !(decideFormula reach (encode backward))
#guard decideFormula reach (encode diagonal)
#guard !(decideFormula reach [])
#guard !(decideFormula reach (encode forward ++ [false]))

def truth : Formula [] 0 := ⟨.truth, trivial⟩
def empty : PointedStructure [] 0 :=
  ⟨⟨0, fun r => Fin.elim0 r⟩, Fin.elim0⟩
#guard decideFormula truth (encode empty)

def nullary : Formula [0] 0 := ⟨.relation 0 Fin.elim0, trivial⟩
def nullaryStructure (b : Bool) : PointedStructure [0] 0 :=
  ⟨⟨0, fun _ _ => b⟩, Fin.elim0⟩
#guard decideFormula nullary (encode (nullaryStructure true))
#guard !(decideFormula nullary (encode (nullaryStructure false)))

#print axioms Lax979537Proofs.LeastFixedPoints.fixedPoint
#print axioms Lax979537Proofs.LeastFixedPoints.least
#print axioms Lax979537Proofs.LeastFixedPoints.finiteConvergence
#print axioms Lax979537Proofs.Positivity.positiveBodyMonotone
#print axioms Lax979537Proofs.StructureEncoding.encodeLength
#print axioms Lax979537Proofs.StructureEncoding.encodeInjective
#print axioms Lax979537Proofs.DecisionProcedure.decideFormula_correct

end VardiImmermanTests
