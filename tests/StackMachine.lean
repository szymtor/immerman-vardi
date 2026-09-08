import Lax979537Proofs.StackUnary

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

end VardiImmermanStackTests
