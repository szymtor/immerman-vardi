import Lax979537.FixedPointSyntax
import Lax979537.LeastFixedPoints

/-!
---
title: Semantics and definability in FO(LFP)
type: definition and theorem
---
First-order operations have their usual semantics. A fixed-point body,
with its parameters held fixed, defines an operator on $k$-ary relations;
the fixed-point formula tests membership of its argument tuple in the least
fixed point of that operator. Positivity of an admissible body implies
monotonicity; this is an explicit proof obligation.

A query is FO(LFP)-definable if one admissible formula defines it on every
finite ordered structure and every assignment to its free variables.
The formula is chosen once for the query, independently of the structure.
-/

namespace Lax979537.FixedPointSemantics

open Lax979537.OrderedStructures Lax979537.FixedPointSyntax
open Lax979537.LeastFixedPoints

abbrev RelationEnv (n : Nat) (ρ : List Nat) :=
  (r : Fin ρ.length) → Set (Fin (ρ.get r) → Fin n)

def extend {n k : Nat} {ρ : List Nat} (R : Set (Fin k → Fin n))
    (η : RelationEnv n ρ) : RelationEnv n (k :: ρ) :=
  Fin.cons R η

def eval {σ : Vocabulary} {m : Nat} {ρ : List Nat}
    (φ : RawFormula σ m ρ) (A : OrderedStructure σ)
    (v : Fin m → Fin A.size) (η : RelationEnv A.size ρ) : Prop :=
  match φ with
  | .truth => True
  | .equal x y => v x = v y
  | .less x y => v x < v y
  | .relation r args => A.relation r (v ∘ args) = true
  | .variable r args => η r (v ∘ args)
  | .neg ψ => ¬ eval ψ A v η
  | .conj ψ χ => eval ψ A v η ∧ eval χ A v η
  | .exists' ψ => ∃ a, eval ψ A (Fin.cons a v) η
  | .lfp _ body args =>
      leastFixedPoint (fun R => {a | eval body A (Fin.append a v) (extend R η)})
        (v ∘ args)

def bodyOperator {σ : Vocabulary} {m k : Nat} {ρ : List Nat}
    (body : RawFormula σ (k + m) (k :: ρ)) (A : OrderedStructure σ)
    (v : Fin m → Fin A.size) (η : RelationEnv A.size ρ) :
    Set (Fin k → Fin A.size) → Set (Fin k → Fin A.size) :=
  fun R => {a | eval body A (Fin.append a v) (extend R η)}

axiom positiveBodyMonotone {σ : Vocabulary} {m k : Nat} {ρ : List Nat}
    (body : RawFormula σ (k + m) (k :: ρ))
    (hbody : body.Admissible) (hpositive : body.positiveAt 0 true)
    (A : OrderedStructure σ) (v : Fin m → Fin A.size)
    (η : RelationEnv A.size ρ) : Monotone (bodyOperator body A v η)

def Satisfies {σ : Vocabulary} {k : Nat} (A : PointedStructure σ k)
    (φ : Formula σ k) : Prop :=
  eval φ.val A.structureValue A.tuple (fun r => Fin.elim0 r)

def Definable {σ : Vocabulary} {k : Nat} (Q : Query σ k) : Prop :=
  ∃ φ : Formula σ k, ∀ A, Q A ↔ Satisfies A φ

end Lax979537.FixedPointSemantics
