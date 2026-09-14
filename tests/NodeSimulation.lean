import Lax751879Proofs.NodeAcceptance

namespace ImmermanVardiNodeTests

open Turing Lax751879Proofs PersistentStack NodeMachine TimedNodes NodeTrace NodeClosure NodeAcceptance

def initialRecords : Heap (Fin 4) Bool := NodeInput.records [(0, true), (1, false)]
def pushedRecords : Heap (Fin 4) Bool := insert (2, false, some 0) initialRecords
def sharedRecords : Heap (Fin 4) Bool := insert (3, true, some 1) pushedRecords

example : Chain initialRecords (some 0) [true, false] :=
  NodeInput.records_chain [(0, true), (1, false)]

example : Functional initialRecords := NodeInput.records_functional _ (by decide)

example : Chain pushedRecords (some 2) [false, true, false] :=
  push_chain (NodeInput.records_chain [(0, true), (1, false)]) 2 false

-- Two different heads can share the same suffix; adding either new node
-- preserves the original stack and every older record.
example : Chain sharedRecords (some 0) [true, false] :=
  (NodeInput.records_chain [(0, true), (1, false)]).mono
    ((Set.subset_insert _ _).trans (Set.subset_insert _ _))

example : Chain sharedRecords (some 3) [true, false] := by
  apply push_chain
  apply Chain.mono (Set.subset_insert _ _)
  exact Chain.cons (by simp [initialRecords, NodeInput.records, NodeInput.head]) Chain.nil

example : Functional sharedRecords := by
  apply insert_functional
  · apply insert_functional
    · exact NodeInput.records_functional _ (by decide)
    · simp [Fresh, initialRecords, NodeInput.records]
  · simp [Fresh, pushedRecords, initialRecords, NodeInput.records]

example : Read sharedRecords (some 2) (some false) (some 0) :=
  Or.inr ⟨2, false, rfl, rfl, by simp [sharedRecords, pushedRecords]⟩

example : Read sharedRecords none none none := Or.inl ⟨rfl, rfl, rfl⟩

def constantMachine (b : Bool) : FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ := fun _ => Bool
  Λ := Unit
  main := ()
  σ := Unit
  initialState := ()
  Γk₀Fin := inferInstance
  m := fun _ => .push () (fun _ => b) .halt

def constant_runs (b : Bool) :
    StateTransition.EvalsToInTime (constantMachine b).step (initList (constantMachine b) [])
      (some (haltList (constantMachine b) [b])) 1 := by
  refine ⟨⟨1, ?_⟩, le_rfl⟩
  change some (TM2.stepAux ((constantMachine b).m ()) () (initList (constantMachine b) []).stk) =
    some (haltList (constantMachine b) [b])
  congr 1

-- The positive fixed point accepts exactly the original machine's output,
-- for both Booleans and every sufficiently large time horizon.
example (a b : Bool) (N : Nat) (hN : TM2Micro.factor (constantMachine b) ≤ N) :
    accepts (closure (input (constantMachine b) [] (Initial := Unit) Fin.elim0
      (by intro i; exact Fin.elim0 i)) N) N () a ↔ a = b := by
  exact accepts_iff (constantMachine b) [] Fin.elim0 (by intro i; exact Fin.elim0 i) b a
    (constant_runs b) (by simpa only [Nat.mul_one] using hN)

#print axioms Lax751879Proofs.PersistentStack.read_correct
#print axioms Lax751879Proofs.NodeMachine.step_sound
#print axioms Lax751879Proofs.NodeInput.represented_run
#print axioms Lax751879Proofs.NodeClosure.closure_eq_trace
#print axioms Lax751879Proofs.NodeAcceptance.accepts_iff

end ImmermanVardiNodeTests
