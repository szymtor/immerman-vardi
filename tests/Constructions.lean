import Lax979537Proofs.FiniteExceptions
import Lax979537Proofs.PositiveRules
import Lax979537Proofs.ComputationTableau
import Lax979537Proofs.EvaluationWork
import Lax979537Proofs.DecisionProcedure
import Mathlib.Data.Fin.VecNotation

namespace ImmermanVardiConstructionTests

open Lax979537.OrderedStructures Lax979537.FixedPointSyntax
open Lax979537Proofs
open Lax979537.StructureEncoding
open DecisionProcedure

def path : OrderedStructure [2] where
  size := 3
  relation := Fin.cons (fun t : Fin 2 → Fin 3 => decide ((t 0).val + 1 = (t 1).val))
    (fun r => Fin.elim0 r)

def identityRule : PositiveRules.Rule [2] 2 where
  numVars := 1
  guard := .truth
  guard_firstOrder := trivial
  head := ![0, 0]
  premises := []

def stepRule : PositiveRules.Rule [2] 2 where
  numVars := 3
  guard := .relation 0 ![0, 1]
  guard_firstOrder := trivial
  head := ![0, 2]
  premises := [![1, 2]]

def reach : Formula [2] 2 := PositiveRules.closure [identityRule, stepRule]

def pathPoint (a : Fin 2 → Fin 3) : PointedStructure [2] 2 := ⟨path, a⟩

#guard evaluatePointed reach (pathPoint ![0, 2])
#guard !(evaluatePointed reach (pathPoint ![2, 0]))
#guard evaluatePointed reach (pathPoint ![1, 1])

#guard evaluatePointed (FiniteExceptions.diagram (pathPoint ![0, 2])) (pathPoint ![0, 2])
#guard !(evaluatePointed (FiniteExceptions.diagram (pathPoint ![0, 2])) (pathPoint ![2, 0]))

def domain (n : Nat) : OrderedStructure [] := ⟨n, fun r => Fin.elim0 r⟩

def addressPoint (a : Fin 4 → Fin 3) : PointedStructure [] 4 := ⟨domain 3, a⟩

def nextAddress : Formula [] 4 :=
  ⟨AddressFormulas.successor ![0, 1] ![2, 3],
    FormulaMacros.firstOrder_admissible _ (AddressFormulas.successor_firstOrder _ _)⟩

-- Carry between coordinates, nonconsecutive addresses, and the upper boundary.
#guard evaluatePointed nextAddress (addressPoint ![0, 2, 1, 0])
#guard !(evaluatePointed nextAddress (addressPoint ![0, 1, 1, 0]))
#guard !(evaluatePointed nextAddress (addressPoint ![2, 2, 0, 0]))

def sizeFormula (n : Nat) : Formula [] 0 :=
  ⟨AddressFormulas.sizeExactly n,
    FormulaMacros.firstOrder_admissible _ (AddressFormulas.sizeExactly_firstOrder n)⟩

#guard evaluatePointed (sizeFormula 0) ⟨domain 0, Fin.elim0⟩
#guard !(evaluatePointed (sizeFormula 0) ⟨domain 1, Fin.elim0⟩)
#guard evaluatePointed (sizeFormula 1) ⟨domain 1, Fin.elim0⟩
#guard !(evaluatePointed (sizeFormula 2) ⟨domain 1, Fin.elim0⟩)

def nullary (b : Bool) : PointedStructure [0] 0 :=
  ⟨⟨0, fun _ _ => b⟩, Fin.elim0⟩

#guard evaluatePointed (FiniteExceptions.diagram (nullary true)) (nullary true)
#guard !(evaluatePointed (FiniteExceptions.diagram (nullary true)) (nullary false))
#guard evaluatePointed (FiniteExceptions.diagram (nullary false)) (nullary false)

def toggle : ComputationTableau.LocalSystem Unit Bool 1 where
  initial _ := false
  neighbor _ _ := ()
  transition _ a := !(a 0)

#guard !(ComputationTableau.run toggle 0 ())
#guard ComputationTableau.run toggle 1 ()
#guard !(ComputationTableau.run toggle 2 ())

example (t : Fin 10) (b : Bool) :
    (t, (), b) ∈ Lax979537.LeastFixedPoints.leastFixedPoint
      (ComputationTableau.operator toggle 10) ↔
    b = ComputationTableau.run toggle t.val () :=
  ComputationTableau.leastFixedPoint_iff toggle (by decide) 10 t () b

#print axioms PolynomialBounds.exists_power
#print axioms EvaluationWork.work_le_input_length
#print axioms ComputationTableau.leastFixedPoint_iff
#print axioms PositiveRules.eval_closure
#print axioms TupleAddresses.address_lt_iff
#print axioms AddressFormulas.eval_successor
#print axioms FiniteExceptions.bounded_definable
#print axioms FiniteExceptions.definable_of_above

end ImmermanVardiConstructionTests
