import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.FinRange

/-!
---
title: Finite ordered relational structures and queries
type: definition
---
A finite relational vocabulary is a finite list of arities. An ordered
structure of size $n$ has universe $\{0,\ldots,n-1\}$, its usual strict
order, and an interpretation of each relation symbol. This is the canonical
representative of a finite linearly ordered structure up to isomorphism.
The order is available to formulas as a distinguished atomic predicate.

A pointed structure additionally carries a $k$-tuple of elements. A $k$-ary
query is a property of these pointed structures; $k=0$ gives Boolean queries.
Empty universes and nullary relation symbols are allowed. The vocabulary and
query arity are fixed independently of the input structure.
-/

namespace Lax979537.OrderedStructures

abbrev Vocabulary := List Nat

/-- Relation symbols are numbered in the order of the vocabulary. -/
abbrev Symbol (σ : Vocabulary) := Fin σ.length

structure OrderedStructure (σ : Vocabulary) where
  size : Nat
  relation : (r : Symbol σ) → (Fin (σ.get r) → Fin size) → Bool

structure PointedStructure (σ : Vocabulary) (k : Nat) where
  structureValue : OrderedStructure σ
  tuple : Fin k → Fin structureValue.size

abbrev Query (σ : Vocabulary) (k : Nat) := PointedStructure σ k → Prop

end Lax979537.OrderedStructures
