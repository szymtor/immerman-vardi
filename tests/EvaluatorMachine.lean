import Lax979537Proofs.StackAtomic
import Lax979537Proofs.StackExists
import Lax979537Proofs.StackRename
import Lax979537Proofs.DecoderCorrectness

namespace VardiImmermanEvaluatorMachineTests

open Lax979537Proofs Lax979537Proofs.StackProgram Lax979537Proofs.StackTransfer
open StackBoolean Turing

def runFuel (tm : FinTM2) : Nat → tm.Cfg → tm.Cfg
  | 0, c => c
  | n + 1, c => match tm.step c with
      | none => c
      | some c' => runFuel tm n c'

def eqBits (a b : List Bool) : Bool := a == b
def evalState (s : ((Unit × Bool) × Bool) × Option Bool) (b : Bool) : Bool :=
  s == ((((), true), b), none)
def unitState (s : Unit × Option Bool) : Bool := s == ((), none)

-- Each iteration emits its coordinate, so this checks traversal order as
-- well as the number of iterations and preservation of the original domain.
def forProgram : BitProgram (Fin 6) Unit :=
  StackFor.forValues 0 1 2 3
    (.seq (.atom (.push 4 (fun _ => false))) (StackCopy.copy 2 4 3))
def forMachine : FinTM2 := machine forProgram 0 4 ((), none)

#guard (List.range 6).all fun n =>
  let s : BitStore (Fin 6) Unit := ⟨((), some false), fun p =>
    if p = 0 then List.replicate n true else
    if p = 4 then [false, true] else if p = 5 then [true, false] else []⟩
  let c := runFuel forMachine ((7 * n + 17) * n + 8) (config (some (entry forProgram)) s)
  c.l.isNone && eqBits (c.stk (0 : Fin 6)) (List.replicate n true) &&
    eqBits (c.stk (4 : Fin 6))
      ((List.range n).reverse.flatMap (fun i => List.replicate i true ++ [false]) ++ [false, true]) &&
    ([1, 2, 3] : List (Fin 6)).all (fun p => eqBits (c.stk p) []) &&
    eqBits (c.stk (5 : Fin 6)) [true, false] && unitState c.var

def atomicProgram (equality : Bool) : EvalProgram (Fin 7) Unit :=
  if equality then StackAtomic.equal 0 1 2 3 4 5 else StackAtomic.less 0 1 2 3 4
def atomicMachine (equality : Bool) : FinTM2 :=
  machine (atomicProgram equality) 0 1 ((((), false), false), some true)

#guard [false, true].all fun equality => (List.range 5).all fun n => (List.range 5).all fun m =>
  let s : EvalStore (Fin 7) Unit := ⟨((((), false), true), some false), fun p =>
    if p = 0 then List.replicate n true else if p = 1 then List.replicate m false else
    if p = 5 then [true, false] else if p = 6 then [false, true, false] else []⟩
  let c := runFuel (atomicMachine equality) (24 * (n + m) + 41)
    (config (some (entry (atomicProgram equality))) s)
  c.l.isNone && (List.finRange 7).all (fun p => eqBits (c.stk p) (s.stk p)) &&
    evalState c.var (if equality then decide (n = m) else decide (n < m))

-- Existential body compares each fresh coordinate against a framed parameter.
def existsProgram : EvalProgram (Fin 10) Unit :=
  StackExists.existsValues 0 1 2 3 4 (StackAtomic.equal 2 5 6 7 8 9)
def existsMachine : FinTM2 := machine existsProgram 0 5 ((((), true), false), none)

def existsStore (n m : Nat) : EvalStore (Fin 10) Unit :=
  ⟨((((), false), true), some true), fun p =>
    if p = 0 then List.replicate n true else if p = 5 then List.replicate m true else
    if p = 4 then [true, false] else if p = 9 then [false, true] else []⟩

#guard (List.range 5).all fun n => (List.range 6).all fun m =>
  let s := existsStore n m
  let c := runFuel existsMachine ((24 * (n + m) + 56) * n + 11)
    (config (some (entry existsProgram)) s)
  c.l.isNone && (List.finRange 10).all (fun p => eqBits (c.stk p) (s.stk p)) &&
    evalState c.var (decide (m < n))

-- A symbolic composition check: the atomic and quantifier contracts combine
-- for every n,m, beyond the finite concrete-machine tests above.
example (n m : Nat) : ∃ cost, cost ≤ (24 * (n + m) + 56) * n + 11 ∧
    Returns existsProgram (existsStore n m) (decide (m < n)) cost := by
  obtain ⟨c, hc, hp⟩ := StackExists.existsValues_returns (existsStore n m)
    (0 : Fin 10) 1 2 3 4 (by decide) (by simp [existsStore])
    (by simp [existsStore]) (by simp [existsStore]) (StackAtomic.equal 2 5 6 7 8 9)
    (fun i => decide (i = m)) n (24 * (n + m) + 41) (by simp [existsStore]) (by
      intro i hi a remaining scratch
      obtain ⟨c, hc, hp⟩ := StackAtomic.equal_returns (2 : Fin 10) 5 6 7 8 9 (by decide)
        (StackFor.pack (StackExists.payload (existsStore n m) 4) 1 2 a i remaining scratch)
        (by simp [StackFor.pack, working, StackExists.payload, existsStore])
        (by simp [StackFor.pack, working, StackExists.payload, existsStore])
        (by simp [StackFor.pack, working, StackExists.payload, existsStore])
      have htwo : (StackFor.pack (StackExists.payload (existsStore n m) 4) 1 2 a i remaining scratch).stk 2 =
          List.replicate i true := by simp [StackFor.pack, working]
      have hfive : (StackFor.pack (StackExists.payload (existsStore n m) 4) 1 2 a i remaining scratch).stk 5 =
          List.replicate m true := by simp [StackFor.pack, working, StackExists.payload, existsStore]
      rw [htwo, hfive, List.length_replicate, List.length_replicate] at hc hp
      exact ⟨c, by omega, hp⟩)
  have he : (List.range n).any (fun i => decide (i = m)) = decide (m < n) := by
    apply Bool.eq_iff_iff.mpr
    simp
  rw [he] at hp
  exact ⟨c, hc, hp⟩

-- The existing full decoder executes inside a larger layout, with populated
-- evaluator stacks outside its port image. Those extra stacks must survive.
abbrev ExtendedPort := FiniteDecoder.Port [2] 2 ⊕ Fin 2
def extendedProgram : EvalProgram ExtendedPort Unit :=
  StackRename.rename Sum.inl (FiniteDecoder.program [2] 2)
def extendedMachine : FinTM2 := machine extendedProgram
  (.inl (FiniteDecoder.work [2] 2).input) (.inl (FiniteDecoder.work [2] 2).domain) FiniteDecoder.initial

def checkExtended (xs : List Bool) : Bool :=
  let s := StackRename.sumStore (FiniteDecoder.inputStore [2] 2 xs)
    (fun p : Fin 2 => if p = 0 then [true, false] else [false, false, true])
  let c := runFuel extendedMachine 3000 (config (some (entry extendedProgram)) s)
  let t := StackDecoder.result (FiniteDecoder.layout [2] 2) (FiniteDecoder.inputStore [2] 2 xs)
  c.l.isNone && evalState c.var t.state.1.2 &&
    (List.finRange 5).all (fun p => eqBits (c.stk (.inl (.inl p))) (t.stk (.inl p))) &&
    (List.finRange 2).all (fun p => eqBits (c.stk (.inl (FiniteDecoder.coordPort [2] 2 p)))
      (t.stk (FiniteDecoder.coordPort [2] 2 p))) &&
    eqBits (c.stk (.inl (FiniteDecoder.tablePort [2] 2 0)))
      (t.stk (FiniteDecoder.tablePort [2] 2 0)) &&
    eqBits (c.stk (.inr (0 : Fin 2))) [true, false] &&
    eqBits (c.stk (.inr (1 : Fin 2))) [false, false, true]

#guard checkExtended [true, true, false, true, false, false, true, false, true, false]
#guard checkExtended []
#guard checkExtended [false, false]
#guard checkExtended [true, false, true, true, false, false]

#print axioms StackFor.forValues_executes
#print axioms StackFor.foldRange_zero_eq
#print axioms StackRename.rename_executes
#print axioms StackRename.executes_in_sum
#print axioms StackBoolean.binary_returns
#print axioms StackAtomic.less_returns
#print axioms StackAtomic.equal_returns
#print axioms StackAtomic.lessValue_returns
#print axioms StackAtomic.equalValue_returns
#print axioms StackExists.existsValues_returns
#print axioms StackExists.any_range_iff

end VardiImmermanEvaluatorMachineTests
