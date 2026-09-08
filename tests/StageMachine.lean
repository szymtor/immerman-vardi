import Lax979537Proofs.StackLfpTables
import Lax979537Proofs.StackSemanticRounds

namespace ImmermanVardiStageMachineTests

open Lax979537Proofs Lax979537Proofs.StackProgram Lax979537Proofs.StackTransfer
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

def stagePool (k : Nat) : List (Fin 10) := [5, 6].take k
def stageBody : BitProgram (Fin 10) Unit :=
  .seq (.atom (.push 7 (fun _ => false))) (StackCopy.copy 3 7 4)
def stageProgram (k : Nat) : BitProgram (Fin 10) Unit :=
  StackStages.stages 0 1 2 3 4 (stagePool k) stageBody
def stageMachine (k : Nat) : FinTM2 := machine (stageProgram k) 0 7 ((), none)

#guard (List.range 4).all fun n => (List.range 3).all fun k =>
  let m := n ^ k
  let s : BitStore (Fin 10) Unit := ⟨((), some false), fun p =>
    if p = 0 then List.replicate n true else if p = 7 then [true, false] else
    if p = 8 then [false, true] else []⟩
  let c := runFuel (stageMachine k) (StackPower.cost k n + (7 * m + 19) * m + 10)
    (config (some (entry (stageProgram k))) s)
  c.l.isNone && unitState c.var &&
    eqBits (c.stk (7 : Fin 10))
      ((List.range m).reverse.flatMap (fun i => List.replicate i true ++ [false]) ++ [true, false]) &&
    (List.finRange 10).all (fun p => p == 7 || eqBits (c.stk p) (s.stk p))

def pool (k : Nat) : List (Fin 16) := [8, 9].take k
def slots (k : Nat) : List (Fin 16 × Fin 16) := [(10, 11), (12, 13)].take k
def toggleHead : EvalProgram (Fin 16) Unit :=
  .atom (.peek 3 (fun s b => (((s.1.1.1, true), !b.getD false), none)))
def lfpProgram (k : Nat) : EvalProgram (Fin 16) Unit :=
  StackLfpTables.run 0 1 2 3 4 5 6 7 (pool k) (slots k) toggleHead
def lfpMachine (k : Nat) : FinTM2 := machine (lfpProgram k) 0 3 ((((), true), false), none)
def initialStore (n : Nat) : EvalStore (Fin 16) Unit :=
  ⟨((((), false), true), some true), fun p =>
    if p = 0 then List.replicate n true else if p = 14 then [true, false] else
    if p = 15 then [false, true, false] else []⟩
def cost (n k : Nat) : Nat :=
  (StackTuples.cost n 3 k + 3 * n ^ k + 3) +
    (StackPower.cost k n + (StackTableStages.roundCost n k 1 + 14) * n ^ k + 10)

-- A toggling transformer deliberately checks the exact number of rounds.
-- This is a test of the general iteration program, not a positive LFP formula.
#guard (List.range 4).all fun n => (List.range 3).all fun k =>
  let s := initialStore n
  let c := runFuel (lfpMachine k) (cost n k) (config (some (entry (lfpProgram k))) s)
  c.l.isNone && evalState c.var &&
    eqBits (c.stk (3 : Fin 16)) (List.replicate (n ^ k) (decide (n ^ k % 2 = 1))) &&
    (List.finRange 16).all (fun p => p == 3 || eqBits (c.stk p) (s.stk p))

def encoded (n : Nat) (a : Bool) : List Bool := List.replicate (n ^ 2) a

-- Instantiate the general table-iteration theorem for arbitrary n. The
-- callback proof reads the current table retained by the actual program.
example (n : Nat) : ∃ c, c ≤ cost n 2 ∧
    Executes (lfpProgram 2) (initialStore n)
      (StackTableStages.family (initialStore n) 3 (encoded n) (((!·)^[n ^ 2]) false)) c := by
  apply StackLfpTables.run_executes (initialStore n) (0 : Fin 16) 1 2 3 4 5 6 7
    (pool 2) (slots 2) (by decide) (by
      intro key hk
      have hn : key ≠ 0 ∧ key ≠ 14 ∧ key ≠ 15 := by
        have hslots : ∀ p ∈ (1 :: 2 :: 3 :: 4 :: 5 :: 6 :: 7 ::
            (pool 2 ++ ports (slots 2))), p ≠ 0 ∧ p ≠ 14 ∧ p ≠ 15 := by decide
        exact hslots key hk
      simp [initialStore, hn.1, hn.2.1, hn.2.2])
    (by decide) (encoded n) (!·) (fun a _ => !a) n 1
    (by intro a; simp [encoded, slots])
    (by intro a; simp [encoded, slots, StackMaterialize.table, tuples_length])
    toggleHead (by simp [initialStore])
  · intro i hi a rem scratch values hlen hvalid remaining hrem bits scratch'
    let s := packTuple (StackMaterialize.payload
      (StackTableStages.running (initialStore n) 3 5 6 7 (encoded n) (n ^ 2) a i rem scratch) 2)
      (slots 2) bits values remaining scratch'
    have hcur : s.stk 3 = List.replicate (n ^ 2) a := by
      rw [packTuple_fresh _ _ 3 (by decide)]
      simp [StackMaterialize.payload, StackTableStages.running, StackFor.pack, working,
        StackStages.prepared, StackTableStages.family, setStack, result, encoded]
    have hpos : 0 < n ^ 2 := by have hi' : i < n ^ 2 := hi; omega
    have hhead : (s.stk 3).head? = some a := by
      rw [hcur]
      obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
      rw [hm, List.replicate_succ]
      rfl
    have hp := Executes.atom (.peek 3 (fun q : ((Unit × Bool) × Bool) × Option Bool => fun b =>
      (((q.1.1.1, true), !b.getD false), none))) s
    have he : Op.apply (.peek 3 (fun q : ((Unit × Bool) × Bool) × Option Bool => fun b =>
        (((q.1.1.1, true), !b.getD false), none))) s = result (!a) s := by
      apply Store.ext
      · simp [Op.apply, result, hhead]
      · rfl
    rw [he] at hp
    exact ⟨1, le_rfl, hp⟩
  · rfl

#guard eqBits (DenseTables.dense ([] : TableEvaluation.Table 0 0)) [false]
#guard DenseTables.predicate (fun _ : Fin 0 → Fin 0 => true) []
#guard !DenseTables.predicate (fun _ : Fin 1 → Fin 0 => true) [0]
#guard eqBits (DenseTables.dense
  (DenseTables.next (fun _ : TableEvaluation.Table 2 2 => fun v => decide (v 0 < v 1)) []))
  [false, true, false, false]

#print axioms StackStages.stages_executes
#print axioms StackInitialTable.initialize_executes
#print axioms StackTableStages.tableStages_executes
#print axioms StackLfpTables.run_executes
#print axioms StackLfpTables.eval_costPolynomial
#print axioms DenseTables.predicate_values
#print axioms DenseTables.valid_values
#print axioms DenseTables.dense_next
#print axioms StackSemanticRounds.semantic_rounds_executes

end ImmermanVardiStageMachineTests
