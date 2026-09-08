import Lax979537Proofs.StackUnary
import Lax979537Proofs.StackCompare
import Lax979537Proofs.StackLookup
import Lax979537Proofs.StackPower

namespace VardiImmermanStackTests

open Lax979537Proofs.StackProgram Lax979537Proofs.StackTransfer
open Turing

/-- Run a concrete machine with ample fuel, retaining a halted configuration. -/
def runFuel (tm : FinTM2) : Nat → tm.Cfg → tm.Cfg
  | 0, c => c
  | n + 1, c => match tm.step c with
      | none => c
      | some c' => runFuel tm n c'

def reverseMachine : FinTM2 :=
  machine (transfer (Aux := Unit) false true) false true ((), none)

def eqBits (xs ys : List Bool) : Bool := xs == ys

def unitState (s : Unit × Option Bool) (b : Option Bool) : Bool := s == ((), b)

def boolState (s : Bool × Option Bool) (b : Bool) : Bool := s == (b, none)

def checkReverse (xs : List Bool) : Bool :=
  let c := runFuel reverseMachine 100 (initList reverseMachine xs)
  c.l.isNone && eqBits (c.stk true) xs.reverse && eqBits (c.stk false) [] &&
    unitState c.var none

#guard checkReverse []
#guard checkReverse [false]
#guard checkReverse [true, false, true, true, false]

def nested : BitProgram Bool Bool :=
  .seq (.atom (.load (fun s => (true, s.2))))
    (.loop (fun s => s.1)
      (.seq (transfer false true) (.atom (.load (fun s => (false, s.2))))))

def nestedMachine : FinTM2 := machine nested false true (false, none)

#guard let c := runFuel nestedMachine 100 (initList nestedMachine [true, false, false]);
  c.l.isNone && eqBits (c.stk true) [false, false, true] &&
    eqBits (c.stk false) [] && boolState c.var false

def conditional : BitProgram Bool Bool :=
  .branch (fun s => s.1) (.atom (.push true (fun _ => true)))
    (.atom (.push true (fun _ => false)))

def branchMachine (b : Bool) : FinTM2 := machine conditional false true (b, none)

#guard let c := runFuel (branchMachine true) 10 (initList (branchMachine true) []);
  c.l.isNone && eqBits (c.stk true) [true]
#guard let c := runFuel (branchMachine false) 10 (initList (branchMachine false) []);
  c.l.isNone && eqBits (c.stk true) [false]

def unaryMachine : FinTM2 :=
  machine (Lax979537Proofs.StackUnary.parse (Aux := Unit) false true) false true ((), none)

#guard let c := runFuel unaryMachine 100 (initList unaryMachine [true, true, false, true, false]);
  c.l.isNone && eqBits (c.stk true) [true, true] &&
    eqBits (c.stk false) [true, false] &&
    unitState c.var (some false)
#guard let c := runFuel unaryMachine 100 (initList unaryMachine [false]);
  c.l.isNone && eqBits (c.stk true) [] &&
    unitState c.var (some false)
#guard let c := runFuel unaryMachine 100 (initList unaryMachine [true, true]);
  c.l.isNone && eqBits (c.stk true) [true, true] &&
    unitState c.var none
#guard let c := runFuel unaryMachine 100 (initList unaryMachine []);
  c.l.isNone && eqBits (c.stk true) [] &&
    unitState c.var none

-- The framed transfer theorem allows arbitrary contents on unrelated stacks.
example (base : Fin 3 → List Bool) (xs ys : List Bool) :
    Executes (transfer (Aux := Unit) (0 : Fin 3) 1)
      (working base 0 1 xs ys () none)
      (working base 0 1 [] (xs.reverse ++ ys) () none) (3 * xs.length + 2) :=
  transfer_executes base 0 1 (by decide) xs ys () none

#print axioms Lax979537Proofs.StackProgram.compile_correct
#print axioms Lax979537Proofs.StackProgram.program_polytime
#print axioms Lax979537Proofs.StackTransfer.transfer_executes
#print axioms Lax979537Proofs.StackTransfer.reverse_polytime
#print axioms Lax979537Proofs.StackUnary.parse_executes
#print axioms Lax979537Proofs.StackUnary.splitUnary_correct

def copyProgram : BitProgram (Fin 4) Unit := Lax979537Proofs.StackCopy.copy 0 1 2
def copyMachine : FinTM2 := machine copyProgram 0 1 ((), none)

def checkCopy (xs ys : List Bool) : Bool :=
  let s := Lax979537Proofs.StackCopy.working3 (fun _ : Fin 4 => [false, true])
    0 1 2 xs ys [] () (some true)
  let c := runFuel copyMachine (7 * xs.length + 4) (config (some (entry copyProgram)) s)
  c.l.isNone && eqBits (c.stk (0 : Fin 4)) xs && eqBits (c.stk (1 : Fin 4)) (xs ++ ys) &&
    eqBits (c.stk (2 : Fin 4)) [] && eqBits (c.stk (3 : Fin 4)) [false, true] && unitState c.var none

#guard checkCopy [] [true]
#guard checkCopy [true, false, false] [false, true]

-- The body deliberately clears scratch. Counter repetition must still finish
-- all iterations, using its own read after each body execution.
def repeatProgram : BitProgram Bool Unit :=
  Lax979537Proofs.StackRepeat.repeatCount false
    (.seq (.atom (.push true (fun _ => true))) (.atom (.load (fun _ => ((), none)))))
def repeatMachine : FinTM2 := machine repeatProgram false true ((), none)

#guard (List.range 6).all fun n =>
  let c := runFuel repeatMachine (5 * n + 10) (initList repeatMachine (List.replicate n false))
  c.l.isNone && eqBits (c.stk false) [] && eqBits (c.stk true) (List.replicate n true) &&
    unitState c.var none

def compareProgram : BitProgram (Fin 3) (Unit × Bool) :=
  Lax979537Proofs.StackCompare.less 0 1
def compareMachine : FinTM2 := machine compareProgram 0 1 (((), false), none)
def comparisonState (s : (Unit × Bool) × Option Bool) (b : Bool) : Bool :=
  s == (((), b), none)

#guard (List.range 5).all fun n => (List.range 5).all fun m =>
  let s := working (fun _ : Fin 3 => [true, false]) 0 1
    (List.replicate n true) (List.replicate m true) ((), true) (some false)
  let c := runFuel compareMachine (5 * (n + m) + 8) (config (some (entry compareProgram)) s)
  c.l.isNone && eqBits (c.stk (0 : Fin 3)) [] && eqBits (c.stk (1 : Fin 3)) [] &&
    eqBits (c.stk (2 : Fin 3)) [true, false] && comparisonState c.var (decide (n < m))

def lookupProgram : BitProgram (Fin 3) (Unit × Option Bool) :=
  Lax979537Proofs.StackLookup.lookup 0 1
def lookupMachine : FinTM2 := machine lookupProgram 0 1 (((), none), none)
def lookupState (s : (Unit × Option Bool) × Option Bool) (b : Option Bool) : Bool :=
  s == (((), b), none)

#guard (List.range 6).all fun n =>
  let bits := [true, false, false, true]
  let s := working (fun _ : Fin 3 => [false, true]) 0 1
    (List.replicate n true) bits ((), some false) (some true)
  let c := runFuel lookupMachine (3 * n + 3) (config (some (entry lookupProgram)) s)
  c.l.isNone && eqBits (c.stk (0 : Fin 3)) [] && eqBits (c.stk (1 : Fin 3)) (bits.drop (n + 1)) &&
    eqBits (c.stk (2 : Fin 3)) [false, true] && lookupState c.var bits[n]?

#print axioms Lax979537Proofs.StackCopy.copy_executes
#print axioms Lax979537Proofs.StackRepeat.repeat_executes
#print axioms Lax979537Proofs.StackRepeat.result_spec
#print axioms Lax979537Proofs.StackClear.clear_store
#print axioms Lax979537Proofs.StackCompare.less_executes
#print axioms Lax979537Proofs.StackLookup.lookup_executes

def powerProgram (k : Nat) : BitProgram (Fin 7) Unit :=
  Lax979537Proofs.StackPower.power 0 1 2 (([3, 4, 5] : List (Fin 7)).take k)
def powerMachine (k : Nat) : FinTM2 := machine (powerProgram k) 0 1 ((), none)

#guard (List.range 4).all fun k => (List.range 4).all fun n =>
  let s : BitStore (Fin 7) Unit := ⟨((), some true), fun p =>
    if p = 0 then List.replicate n true else
    if p = 1 then [false] else if p = 6 then [false, true] else []⟩
  let fuel := Lax979537Proofs.StackPower.cost k n
  let c := runFuel (powerMachine k) fuel (config (some (entry (powerProgram k))) s)
  c.l.isNone && eqBits (c.stk (0 : Fin 7)) (List.replicate n true) &&
    eqBits (c.stk (1 : Fin 7)) (List.replicate (n ^ k) true ++ [false]) &&
    ([2, 3, 4, 5] : List (Fin 7)).all (fun p => eqBits (c.stk p) []) &&
    eqBits (c.stk (6 : Fin 7)) [false, true] && unitState c.var none

#print axioms Lax979537Proofs.StackCopy.copy_store
#print axioms Lax979537Proofs.StackPower.power_executes

end VardiImmermanStackTests
