import Lax751879Proofs.StackMaterialize
import Lax751879Proofs.StackAtomic
import Lax751879Proofs.StackTableRound

namespace ImmermanVardiTupleMachineTests

open Lax751879Proofs Lax751879Proofs.StackProgram Lax751879Proofs.StackTransfer
open StackBoolean StackTuples Turing

def runFuel (tm : FinTM2) : Nat → tm.Cfg → tm.Cfg
  | 0, c => c
  | n + 1, c => match tm.step c with
      | none => c
      | some c' => runFuel tm n c'

def eqBits (a b : List Bool) : Bool := a == b
def unitState (s : Unit × Option Bool) : Bool := s == ((), none)
def evalState (s : ((Unit × Bool) × Bool) × Option Bool) : Bool :=
  s == ((((), true), false), none)

def tupleSlots (k : Nat) : List (Fin 11 × Fin 11) := ([(4, 5), (6, 7), (8, 9)]).take k

def emitCoords : List (Fin 11) → BitProgram (Fin 11) Unit
  | [] => .atom (.push 2 (fun _ => false))
  | coord :: cs => .seq (.atom (.push 2 (fun _ => false)))
      (.seq (StackCopy.copy coord 2 1) (emitCoords cs))

def tupleProgram (k : Nat) : BitProgram (Fin 11) Unit :=
  forTuples 0 1 (emitCoords ((tupleSlots k).map Prod.snd)) (tupleSlots k)
def tupleMachine (k : Nat) : FinTM2 := machine (tupleProgram k) 0 2 ((), none)

def checkTuples (n k : Nat) : Bool :=
  let s : BitStore (Fin 11) Unit := ⟨((), some true), fun p =>
    if p = 0 then List.replicate n true else if p = 2 then [true, false] else
    if p = 10 then [false, true] else []⟩
  let c := runFuel (tupleMachine k) (StackTuples.cost n (k * (7 * n + 5) + 1) k)
    (config (some (entry (tupleProgram k))) s)
  let expected := (tuples n k).reverse.flatMap (fun xs =>
    false :: xs.reverse.flatMap (fun i => List.replicate i true ++ [false])) ++ [true, false]
  c.l.isNone && eqBits (c.stk (2 : Fin 11)) expected && unitState c.var &&
    (List.finRange 11).all (fun p => p == 2 || eqBits (c.stk p) (s.stk p))

#guard (List.range 4).all fun n => (List.range 4).all (checkTuples n)

def tableSlots (k : Nat) : List (Fin 13 × Fin 13) := ([(4, 5), (6, 7)]).take k
def tableBody (k : Nat) : EvalProgram (Fin 13) Unit :=
  if k = 0 then answer true else if k = 1 then StackAtomic.equalValue 5 5 8 9 10 11
  else StackAtomic.less 5 7 8 9 10
def tableProgram (k : Nat) : EvalProgram (Fin 13) Unit :=
  StackMaterialize.materialize 0 1 2 3 (tableSlots k) (tableBody k)
def tableMachine (k : Nat) : FinTM2 := machine (tableProgram k) 0 3 ((((), true), false), none)
def tableStore (n : Nat) : EvalStore (Fin 13) Unit :=
  ⟨((((), false), true), some true), fun p =>
    if p = 0 then List.replicate n true else if p = 3 then [false, true] else
    if p = 11 then [true, false, true] else if p = 12 then [false, false, true] else []⟩

def checkTable (n k : Nat) : Bool :=
  let s := tableStore n
  let c := runFuel (tableMachine k) (StackTuples.cost n (48 * n + 43) k + 3 * n ^ k + 3)
    (config (some (entry (tableProgram k))) s)
  let expected := (tuples n k).map (fun xs => if k < 2 then true else
    decide (xs.headD 0 < xs.tail.headD 0))
  c.l.isNone && eqBits (c.stk (3 : Fin 13)) (expected ++ [false, true]) && evalState c.var &&
    (List.finRange 13).all (fun p => p == 3 || eqBits (c.stk p) (s.stk p))

#guard (List.range 4).all fun n => (List.range 3).all (checkTable n)

-- The materialization contract can be discharged by a real atomic evaluator
-- for arbitrary domain size, with arbitrary previously emitted rows.
example (n : Nat) : ∃ c, c ≤ StackTuples.cost n (24 * n + 21) 2 + 3 * n ^ 2 + 3 ∧
    Executes (tableProgram 2) (tableStore n)
      (setStack (result false (tableStore n)) 3
        ((tuples n 2).map (fun xs => decide (xs.headD 0 < xs.tail.headD 0)) ++ [false, true])) c := by
  apply StackMaterialize.materialize_executes (tableStore n) (0 : Fin 13) 1 2 3
    (tableSlots 2) (by decide) (by
      intro key hk
      simp only [tableSlots, List.take_succ_cons, List.take_zero, ports,
        List.flatMap_cons, List.flatMap_nil, List.cons_append, List.nil_append, List.mem_cons,
        List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [tableStore])
    (tableBody 2) (fun xs => decide (xs.headD 0 < xs.tail.headD 0)) n (24 * n + 19)
    (by simp [tableStore])
  intro values hlen hvalid remaining hrem bits scratch
  have hlen' : values.length = 2 := hlen
  obtain ⟨i, j, rfl⟩ : ∃ i j, values = [i, j] := by
    cases values with
    | nil => simp at hlen'
    | cons i vs =>
      cases vs with
      | nil => simp at hlen'
      | cons j rest =>
        have hr : rest = [] := List.length_eq_zero_iff.mp (by simpa using hlen')
        subst rest
        exact ⟨i, j, rfl⟩
  have hi := hvalid i (by simp)
  have hj := hvalid j (by simp)
  let s := packTuple (StackMaterialize.payload (tableStore n) 2) (tableSlots 2)
    bits [i, j] remaining scratch
  obtain ⟨c, hc, hp⟩ := StackAtomic.less_returns (5 : Fin 13) 7 8 9 10 (by decide) s
    (by simp [s, tableSlots, packTuple, StackFor.pack, working, StackMaterialize.payload,
      setStack, result, tableStore, withScratch])
    (by simp [s, tableSlots, packTuple, StackFor.pack, working, StackMaterialize.payload,
      setStack, result, tableStore, withScratch])
    (by simp [s, tableSlots, packTuple, StackFor.pack, working, StackMaterialize.payload,
      setStack, result, tableStore, withScratch])
  have hleft : s.stk 5 = List.replicate i true := by
    simp [s, tableSlots, packTuple, StackFor.pack, working, withScratch]
  have hright : s.stk 7 = List.replicate j true := by
    simp [s, tableSlots, packTuple, StackFor.pack, working, withScratch]
  rw [hleft, hright, List.length_replicate, List.length_replicate] at hc hp
  exact ⟨c, by omega, hp⟩

def roundSlots (k : Nat) : List (Fin 14 × Fin 14) := ([(4, 5), (6, 7)]).take k
def peekCurrent : EvalProgram (Fin 14) Unit :=
  .atom (.peek 13 (fun s b => (((s.1.1.1, true), b.getD false), none)))
def roundProgram (k : Nat) : EvalProgram (Fin 14) Unit :=
  StackTableRound.round 0 1 2 13 3 (roundSlots k) peekCurrent
def roundMachine (k : Nat) : FinTM2 := machine (roundProgram k) 0 13 ((((), true), false), none)

-- Read the old table on every callback. Clearing it before constructing all
-- rows would give incorrect results for the old tables beginning with true.
def checkRound (n k : Nat) (old : List Bool) : Bool :=
  let s : EvalStore (Fin 14) Unit := ⟨((((), false), true), some true), fun p =>
    if p = 0 then List.replicate n true else if p = 13 then old else
    if p = 11 then [true, false] else if p = 12 then [false, true, false] else []⟩
  let c := runFuel (roundMachine k) (StackTuples.cost n 3 k + 9 * n ^ k + 2 * old.length + 9)
    (config (some (entry (roundProgram k))) s)
  c.l.isNone && eqBits (c.stk (13 : Fin 14)) (List.replicate (n ^ k) (old.head?.getD false)) &&
    evalState c.var && (List.finRange 14).all (fun p => p == 13 || eqBits (c.stk p) (s.stk p))

#guard (List.range 4).all fun n => (List.range 3).all fun k =>
  [[], [true, false], [false, true, false]].all (checkRound n k)

def roundLessProgram : EvalProgram (Fin 14) Unit :=
  StackTableRound.round 0 1 2 13 3 (roundSlots 2) (StackAtomic.less 5 7 8 9 10)
def roundLessMachine : FinTM2 := machine roundLessProgram 0 13 ((((), true), false), none)

-- A nonconstant next table detects an accidental reversal during replacement.
#guard (List.range 4).all fun n =>
  let s : EvalStore (Fin 14) Unit := ⟨((((), false), true), some true), fun p =>
    if p = 0 then List.replicate n true else if p = 13 then [true, false, true] else []⟩
  let c := runFuel roundLessMachine (StackTuples.cost n (24 * n + 21) 2 + 9 * n ^ 2 + 15)
    (config (some (entry roundLessProgram)) s)
  c.l.isNone && evalState c.var &&
    eqBits (c.stk (13 : Fin 14)) ((tuples n 2).map (fun xs => decide (xs.headD 0 < xs.tail.headD 0))) &&
    (List.finRange 14).all (fun p => p == 13 || eqBits (c.stk p) (s.stk p))

#print axioms StackTuples.forTuples_executes
#print axioms StackTuples.tuples_eq_canonical
#print axioms StackTuples.eval_costPolynomial
#print axioms StackMaterialize.materialize_executes
#print axioms StackMaterialize.eval_costPolynomial
#print axioms StackTableRound.round_executes

end ImmermanVardiTupleMachineTests
