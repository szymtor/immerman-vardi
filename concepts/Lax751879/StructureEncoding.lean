import Lax751879.OrderedStructures

/-!
---
title: Binary encodings of ordered structures and tuples
type: definition and theorem
---
Encode a structure of size $n$ by $n$ one-bits and a zero-bit, followed by
the characteristic tables of its relations in vocabulary order. Each table
lists tuples in lexicographic order. The distinguished order is determined
by $n$ and needs no table. Append each coordinate $a_i$ of the query tuple
as $a_i$ one-bits and a zero-bit.

The fixed vocabulary and query arity determine all table boundaries. The
encoding is injective and has length
$n+1+\sum_{R\in\sigma}n^{\operatorname{arity}(R)}+\sum_{i<k}(a_i+1)$.
In particular, the length is at least $n$ and polynomial in $n$ for a fixed
vocabulary and arity, including empty vocabularies and small universes.
-/

namespace Lax751879.StructureEncoding

open Lax751879.OrderedStructures

/-- All tuples, with the first coordinate varying slowest. -/
def tuples (n : Nat) : (k : Nat) → List (Fin k → Fin n)
  | 0 => [Fin.elim0]
  | k + 1 => (List.finRange n).flatMap fun a =>
      (tuples n k).map (Fin.cons a)

def unary (n : Nat) : List Bool := List.replicate n true ++ [false]

def encode {σ : Vocabulary} {k : Nat} (A : PointedStructure σ k) : List Bool :=
  unary A.structureValue.size ++
    (List.finRange σ.length).flatMap (fun r =>
      (tuples A.structureValue.size (σ.get r)).map (A.structureValue.relation r)) ++
    (List.finRange k).flatMap (fun i => unary (A.tuple i).val)

axiom encodeInjective (σ : Vocabulary) (k : Nat) :
    Function.Injective (@encode σ k)

axiom encodeLength {σ : Vocabulary} {k : Nat} (A : PointedStructure σ k) :
    (encode A).length = A.structureValue.size + 1 +
      (σ.map (fun r => A.structureValue.size ^ r)).sum +
      ((List.finRange k).map (fun i => (A.tuple i).val + 1)).sum

end Lax751879.StructureEncoding
