import Lax751879Proofs.StackInitialTable
import Lax751879Proofs.StackTableStages

namespace Lax751879Proofs.StackLfpTables

open StackProgram StackTransfer StackTuples StackBoolean StackTableStages

variable {K Aux α : Type} [DecidableEq K]

def run (domain tmp rev current next bound counter coord : K)
    (powerCounters : List K) (tupleSlots : List (K × K)) (body : EvalProgram K Aux) : EvalProgram K Aux :=
  .seq (StackInitialTable.emptyTable domain tmp rev current tupleSlots)
    (tableStages domain tmp rev current next bound counter coord powerCounters tupleSlots body)

noncomputable def costPolynomial (B : Polynomial Nat) (k : Nat) : Polynomial Nat :=
  StackTuples.costPolynomial 3 k + 3 * Polynomial.X ^ k + 3 + StackTableStages.costPolynomial B k

theorem eval_costPolynomial (B : Polynomial Nat) (n k : Nat) :
    (costPolynomial B k).eval n =
      (StackTuples.cost n 3 k + 3 * n ^ k + 3) +
        (StackPower.cost k n + (roundCost n k (B.eval n) + 14) * n ^ k + 10) := by
  simp [costPolynomial, StackTuples.eval_costPolynomial, StackTableStages.eval_costPolynomial]

set_option maxHeartbeats 800000 in
/-- Build the all-false initial table, then run n^k materialized rounds of
the represented transformer. The table is retained for the final lookup;
every other stack is restored. This theorem supplies the iterative part of
the LFP evaluator given the recursive body evaluator's bounded executions. -/
theorem run_executes (s : EvalStore K Aux)
    (domain tmp rev current next bound counter coord : K)
    (powerCounters : List K) (tupleSlots : List (K × K))
    (hsep : (domain :: tmp :: rev :: current :: next :: bound :: counter :: coord ::
      (powerCounters ++ ports tupleSlots)).Nodup)
    (hempty : ∀ key, key ∈ tmp :: rev :: current :: next :: bound :: counter :: coord ::
      (powerCounters ++ ports tupleSlots) → s.stk key = [])
    (hk : powerCounters.length = tupleSlots.length)
    (encode : α → List Bool) (step : α → α) (b : α → List Nat → Bool)
    (n B : Nat) (hlength : ∀ a, (encode a).length = n ^ tupleSlots.length)
    (hstep : ∀ a, encode (step a) = StackMaterialize.table n tupleSlots.length (b a))
    (body : EvalProgram K Aux) (hdomain : s.stk domain = List.replicate n true)
    (hbody : ∀ i, i < n ^ tupleSlots.length → ∀ a rem scratch,
      ∀ values, values.length = tupleSlots.length → (∀ j ∈ values, j < n) →
      ∀ remaining, remaining.length = tupleSlots.length → ∀ bits scratch',
      ∃ c, c ≤ B ∧ Returns body
        (packTuple (StackMaterialize.payload
          (running s current bound counter coord encode (n ^ tupleSlots.length) a i rem scratch) rev)
          tupleSlots bits values remaining scratch') (b a values) c)
    (initial : α) (hzero : encode initial = List.replicate (n ^ tupleSlots.length) false) :
    ∃ c, c ≤ (StackTuples.cost n 3 tupleSlots.length + 3 * n ^ tupleSlots.length + 3) +
        (StackPower.cost tupleSlots.length n +
          (roundCost n tupleSlots.length B + 14) * n ^ tupleSlots.length + 10) ∧
      Executes (run domain tmp rev current next bound counter coord powerCounters tupleSlots body) s
        (family s current encode ((step^[n ^ tupleSlots.length]) initial)) c := by
  have hinit : (domain :: tmp :: rev :: current :: ports tupleSlots).Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.mem_append, not_or, List.nodup_append] at hsep ⊢
    tauto
  obtain ⟨a, ha, hp⟩ := StackInitialTable.initialize_executes s domain tmp rev current tupleSlots hinit
    (by
      intro key hm
      apply hempty key
      simp only [List.mem_cons, List.mem_append] at hm ⊢
      tauto) n hdomain
  have he : setStack (result false s) current (List.replicate (n ^ tupleSlots.length) false) =
      family s current encode initial := by rw [family, hzero]
  rw [he] at hp
  obtain ⟨c, hc, hq⟩ := tableStages_executes s domain tmp rev current next bound counter coord
    powerCounters tupleSlots hsep
    (by
      intro key hm
      apply hempty key
      simp only [List.mem_cons, List.mem_append] at hm ⊢
      tauto)
    hk encode step b n B hlength hstep body hdomain hbody initial
  exact ⟨a + c, Nat.add_le_add ha hc, Executes.seq hp hq⟩

end Lax751879Proofs.StackLfpTables
