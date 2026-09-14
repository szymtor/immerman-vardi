import Lax751879Proofs.ParameterizedRules

open Lax751879.OrderedStructures Lax751879.FixedPointSemantics
open Lax751879Proofs

namespace ParameterizedRulesTest

def seed (σ : Vocabulary) (m : Nat) : ParameterizedRules.Rule σ m m where
  numVars := m
  guard := .truth
  guard_firstOrder := trivial
  head := id
  premises := []
  parameters := id

theorem seed_operator (σ : Vocabulary) (m : Nat) (A : OrderedStructure σ) (q : Fin m → Fin A.size) :
    ParameterizedRules.operator [seed σ m] A q = fun _ => {q} := by
  funext R
  ext a
  simp [ParameterizedRules.operator, ParameterizedRules.Rule.holds, seed, eval, eq_comm]

theorem seed_closure (σ : Vocabulary) (m : Nat) (A : OrderedStructure σ) (q : Fin m → Fin A.size) :
    Lax751879.LeastFixedPoints.leastFixedPoint (ParameterizedRules.operator [seed σ m] A q) = {q} := by
  rw [seed_operator]
  exact (LeastFixedPoints.fixedPoint (fun _ : Set (Fin m → Fin A.size) => {q})
    (fun _ _ _ => Set.Subset.refl _)).symm

@[reducible] def three : OrderedStructure [] := ⟨3, fun r => Fin.elim0 r⟩

/-- A seed at parameter zero cannot be used by a different target vertex. -/
example : ¬eval (ParameterizedRules.membership [seed [] 1]
    (fun _ => (0 : Fin 2)) (fun _ => (1 : Fin 2))) three
    (fun i : Fin 2 => if i.val = 0 then (0 : Fin 3) else 1) (fun i => Fin.elim0 i) := by
  rw [ParameterizedRules.eval_membership, seed_closure]
  intro h
  exact (by decide : (1 : Fin 3) ≠ 0) (congrFun h 0)

example : eval (ParameterizedRules.membership [seed [] 1]
    (fun _ => (0 : Fin 2)) (fun _ => (0 : Fin 2))) three
    (fun i : Fin 2 => if i.val = 0 then (0 : Fin 3) else 1) (fun i => Fin.elim0 i) := by
  rw [ParameterizedRules.eval_membership, seed_closure]
  rfl

/-- The zero-parameter, zero-arity case also works on an empty universe. -/
example : eval (ParameterizedRules.membership [seed [] 0] Fin.elim0 Fin.elim0)
    (⟨0, fun r => Fin.elim0 r⟩ : OrderedStructure []) Fin.elim0 (fun i => Fin.elim0 i) := by
  rw [ParameterizedRules.eval_membership, seed_closure]
  exact Subsingleton.elim _ _

#print axioms ParameterizedRules.Rule.eval_formula
#print axioms ParameterizedRules.bodyOperator_eq
#print axioms ParameterizedRules.eval_membership

end ParameterizedRulesTest
