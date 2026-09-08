import Lax979537Proofs.StackLfpValue
import Lax979537Proofs.StackAtomic

namespace ImmermanVardiLookupMachineTests

open Lax979537Proofs Lax979537Proofs.StackProgram Lax979537Proofs.StackTransfer
open StackBoolean StackTuples Turing

def runFuel (tm : FinTM2) : Nat → tm.Cfg → tm.Cfg
  | 0, c => c
  | n + 1, c => match tm.step c with
      | none => c
      | some c' => runFuel tm n c'

def eqBits (a b : List Bool) : Bool := a == b
def unitState (s : Unit × Option Bool) : Bool := s == ((), none)
def evalState (s : ((Unit × Bool) × Bool) × Option Bool) (b : Bool) : Bool :=
  s == ((((), true), b), none)

def hornerProgram : BitProgram (Fin 6) Unit := StackHorner.step 0 1 2 3 4
def hornerMachine : FinTM2 := machine hornerProgram 0 1 ((), none)

#guard (List.range 4).all fun n => (List.range 4).all fun a => (List.range 4).all fun v =>
  let s : BitStore (Fin 6) Unit := ⟨((), some true), fun p =>
    if p = 0 then List.replicate n true else if p = 1 then List.replicate a true else
    if p = 4 then List.replicate v true else if p = 5 then [false, true] else []⟩
  let c := runFuel hornerMachine ((7 * n + 9) * a + 7 * v + 8) (config (some (entry hornerProgram)) s)
  c.l.isNone && unitState c.var && eqBits (c.stk (1 : Fin 6)) (List.replicate (n * a + v) true) &&
    (List.finRange 6).all (fun p => p == 1 || eqBits (c.stk p) (s.stk p))

def indexProgram : BitProgram (Fin 8) Unit := StackIndex.build 0 1 2 3 [4, 5, 4]
def indexMachine : FinTM2 := machine indexProgram 0 1 ((), none)

#guard (List.range 4).all fun n => (List.range (n + 1)).all fun a => (List.range (n + 1)).all fun b =>
  let s : BitStore (Fin 8) Unit := ⟨((), some false), fun p =>
    if p = 0 then List.replicate n true else if p = 4 then List.replicate a true else
    if p = 5 then List.replicate b true else if p = 7 then [true, false] else []⟩
  let c := runFuel indexMachine (StackIndex.budget n 3) (config (some (entry indexProgram)) s)
  c.l.isNone && unitState c.var && eqBits (c.stk (1 : Fin 8)) (List.replicate (n * (n * a + b) + a) true) &&
    (List.finRange 8).all (fun p => p == 1 || eqBits (c.stk p) (s.stk p))

def bitProgram : EvalProgram (Fin 5) Unit := StackReadBit.readBit 0 1 2 3
def bitMachine : FinTM2 := machine bitProgram 0 1 ((((), true), false), none)

#guard (List.range 8).all fun m => [[], [true], [false, true, true, false, true]].all fun bits =>
  let s : EvalStore (Fin 5) Unit := ⟨((((), false), true), some true), fun p =>
    if p = 0 then bits else if p = 1 then List.replicate m false else
    if p = 4 then [true, false] else []⟩
  let c := runFuel bitMachine (9 * bits.length + 3 * m + 9) (config (some (entry bitProgram)) s)
  c.l.isNone && evalState c.var (bits[m]?.getD false) && eqBits (c.stk (1 : Fin 5)) [] &&
    (List.finRange 5).all (fun p => p == 1 || eqBits (c.stk p) (s.stk p))

def coords (k : Nat) : List (Fin 10) := if k = 3 then [6, 7, 6] else [6, 7].take k
def lookupProgram (k : Nat) : EvalProgram (Fin 10) Unit := StackTableLookup.lookup 0 1 2 3 4 5 (coords k)
def lookupMachine (k : Nat) : FinTM2 := machine (lookupProgram k) 0 1 ((((), true), false), none)
def predicate (n : Nat) (flip : Bool) (xs : List Nat) : Bool := flip != decide (TupleRank.rank n xs % 3 = 1)

def checkLookup (n k a b : Nat) (flip : Bool) : Bool :=
  let bits := (tuples n k).map (predicate n flip)
  let s : EvalStore (Fin 10) Unit := ⟨((((), false), true), some true), fun p =>
    if p = 0 then List.replicate n true else if p = 1 then bits else
    if p = 6 then List.replicate a true else if p = 7 then List.replicate b true else
    if p = 8 then [true, false] else if p = 9 then [false] else []⟩
  let c := runFuel (lookupMachine k) (StackIndex.budget n k + 12 * n ^ k + 9)
    (config (some (entry (lookupProgram k))) s)
  let query := (coords k).map (fun p => if p = 6 then a else b)
  c.l.isNone && evalState c.var (predicate n flip query) &&
    (List.finRange 10).all (fun p => eqBits (c.stk p) (s.stk p))

#guard [false, true].all (checkLookup 0 0 0 0)
#guard (List.range 4).all fun n => (List.range 4).all fun k =>
  (List.range n).all fun a => (List.range n).all fun b => [false, true].all (checkLookup n k a b)

def lfpArgs (repeated : Bool) : List (Fin 20) := if repeated then [14, 14] else [14, 15]
def lfpProgram (repeated : Bool) : EvalProgram (Fin 20) Unit :=
  StackLfpValue.evaluate 0 1 2 3 4 5 6 7 [8, 9] [(10, 11), (12, 13)] (lfpArgs repeated)
    (StackAtomic.less 11 13 16 17 18)
def lfpMachine (repeated : Bool) : FinTM2 := machine (lfpProgram repeated) 0 3 ((((), true), false), none)
def lfpCost (n : Nat) : Nat :=
  (StackTuples.cost n 3 2 + 3 * n ^ 2 + 3) +
    (StackPower.cost 2 n + (StackTableStages.roundCost n 2 (24 * n + 19) + 14) * n ^ 2 + 10) +
    StackIndex.budget n 2 + 14 * n ^ 2 + 11

-- A constant, monotone table transformer with body x < y exercises the
-- complete LFP constructor, final tuple lookup, and deletion of its table.
#guard (List.range 4).all fun n => (List.range n).all fun a => (List.range n).all fun b =>
  [false, true].all fun repeated =>
  let s : EvalStore (Fin 20) Unit := ⟨((((), false), true), some true), fun p =>
    if p = 0 then List.replicate n true else if p = 14 then List.replicate a true else
    if p = 15 then List.replicate b true else if p = 19 then [false, true, false] else []⟩
  let c := runFuel (lfpMachine repeated) (lfpCost n) (config (some (entry (lfpProgram repeated))) s)
  c.l.isNone && evalState c.var (decide (a < if repeated then a else b)) &&
    (List.finRange 20).all (fun p => eqBits (c.stk p) (s.stk p))

#print axioms StackHorner.step_executes
#print axioms StackIndex.build_executes
#print axioms TupleRank.rank_address
#print axioms TupleRank.canonical_at_address
#print axioms TupleRank.table_at_rank
#print axioms StackReadBit.readBit_executes
#print axioms StackTableLookup.lookup_returns
#print axioms StackLfpValue.evaluate_returns

end ImmermanVardiLookupMachineTests
