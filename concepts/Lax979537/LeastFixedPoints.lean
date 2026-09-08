import Mathlib.Data.Set.Lattice
import Mathlib.Data.Fintype.Card

/-!
---
title: Least fixed points on finite relations
type: definition and theorem
---
For a monotone operator $F$ on sets, its least fixed point is the intersection
of all sets $R$ satisfying $F(R)\subseteq R$. Starting from the empty set,
iterate $F$. On a finite set of $N$ possible elements, stage $N$ is already
the least fixed point. For a $k$-ary relation on an $n$-element universe,
there are $n^k$ possible tuples.

The intersection definition is total even for nonmonotone operators; the
fixed-point and convergence statements explicitly require monotonicity.
-/

namespace Lax979537.LeastFixedPoints

def leastFixedPoint {α : Type} (F : Set α → Set α) : Set α :=
  sInf {R | F R ⊆ R}

def stage {α : Type} (F : Set α → Set α) : Nat → Set α
  | 0 => ∅
  | t + 1 => F (stage F t)

axiom fixedPoint {α : Type} (F : Set α → Set α) (hF : Monotone F) :
    F (leastFixedPoint F) = leastFixedPoint F

axiom least {α : Type} (F : Set α → Set α) (R : Set α)
    (hR : F R ⊆ R) : leastFixedPoint F ⊆ R

axiom finiteConvergence {α : Type} [Fintype α]
    (F : Set α → Set α) (hF : Monotone F) :
    stage F (Fintype.card α) = leastFixedPoint F

end Lax979537.LeastFixedPoints
