import Lax979537Proofs.TM2MicroSupport
import Mathlib.Data.Fin.VecNotation

namespace ImmermanVardiTM2MicroTests

open Turing Lax979537Proofs TM2Micro

@[reducible] def Alphabet (k : Fin 2) : Type := if k = 0 then Bool else Nat

def code (l : Fin 2) : TM2.Stmt Alphabet (Fin 2) Bool :=
  if l = 0 then
    .pop 0 (fun _ b => b.getD false)
      (.push 1 (fun b => (if b then 7 else 13 : Nat))
        (.load (! ·)
          (.peek 1 (fun _ (a : Option Nat) => a == some 7)
            (.branch id (.goto (fun _ => 1)) (.load (! ·) (.goto (fun _ => 1)))))))
  else .pop 1 (fun _ (a : Option Nat) => a == some 7) (.push 0 id .halt)

/-- The internal stack alphabet is genuinely infinite (Nat); the reachable
symbols are nevertheless finite, as required by the general theorem. -/
def tm : FinTM2 where
  K := Fin 2
  k₀ := 0
  k₁ := 0
  Γ := Alphabet
  Λ := Fin 2
  main := 0
  σ := Bool
  initialState := false
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := code

def halted (c : Cfg tm.Γ tm.Λ tm.σ) : Bool :=
  match c.cursor with | .boundary none => true | _ => false
def boolEq (a b : Bool) : Bool := a == b
def boolBits (a b : List Bool) : Bool := a == b
def natBits (a b : List Nat) : Bool := a == b

#guard [false, true].all fun b =>
  let c := (next tm.m)^[12] (boundary (initList tm [b]))
  halted c && boolEq c.var b && boolBits (c.stk (0 : Fin 2)) [b] && natBits (c.stk (1 : Fin 2)) []

-- The false branch performs one extra load; swapping branch selection
-- would be detected by these different termination times.
#guard halted ((next tm.m)^[11] (boundary (initList tm [true])))
#guard !(halted ((next tm.m)^[11] (boundary (initList tm [false]))))

#guard [false, true].all fun b =>
  let c := (next tm.m)^[100] (boundary (initList tm [b]))
  halted c && boolEq c.var b && boolBits (c.stk (0 : Fin 2)) [b] && natBits (c.stk (1 : Fin 2)) []

-- Observe a pushed Nat before the subsequent pop, checking that pop/peek
-- control changes and branching are split into separate real operations.
#guard [false, true].all fun b =>
  let c := (next tm.m)^[3] (boundary (initList tm [b]))
  natBits (c.stk (1 : Fin 2)) [if b then 7 else 13] && boolBits (c.stk (0 : Fin 2)) []

example (b : Bool) (n : Nat) :
    TM2Alphabet.Valid (TM2Alphabet.alphabet tm : Set (Sigma tm.Γ))
      (((next tm.m)^[n] (boundary (initList tm [b]))).stk) :=
  (TM2MicroSupport.initial_run_support tm [b] n).2

example (q : TM2.Stmt tm.Γ tm.Λ tm.σ) (v : tm.σ) (stk : (k : tm.K) → List (tm.Γ k)) :
    ∃ t, t ≤ weight q ∧ (next tm.m)^[t] (instruction q v stk) = boundary (TM2.stepAux q v stk) :=
  statement_refines tm.m q v stk

example (xs : List (tm.Γ tm.k₀)) {d : tm.Cfg} {T N : Nat}
    (h : StateTransition.EvalsToInTime tm.step (initList tm xs) (some d) T)
    (hd : d.l = none) (hN : factor tm * T ≤ N) :
    (next tm.m)^[N] (boundary (initList tm xs)) = boundary d := evals_at_time tm h hd hN

#print axioms Lax979537Proofs.TM2Alphabet.evals_valid
#print axioms Lax979537Proofs.TM2Micro.evals_refines
#print axioms Lax979537Proofs.TM2Micro.evals_at_time
#print axioms Lax979537Proofs.TM2MicroSupport.initial_run_support
#print axioms Lax979537Proofs.TM2MicroSupport.initial_length

end ImmermanVardiTM2MicroTests
