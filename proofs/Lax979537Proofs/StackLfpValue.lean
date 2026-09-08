import Lax979537Proofs.StackSemanticRounds
import Lax979537Proofs.StackTableLookup

namespace Lax979537Proofs.StackLfpValue

open StackProgram StackTransfer StackTuples StackBoolean StackTableStages DenseTables

variable {K Aux : Type} [DecidableEq K]

/-- Materialize the fixed number of rounds, read the queried tuple's bit,
and delete the private final table. Stage workspace is reused for lookup. -/
def evaluate (domain tmp rev current nextPort bound counter coord : K)
    (powerCounters : List K) (tupleSlots : List (K × K)) (args : List K)
    (body : EvalProgram K Aux) : EvalProgram K Aux :=
  .seq (StackLfpTables.run domain tmp rev current nextPort bound counter coord powerCounters tupleSlots body)
    (.seq (StackTableLookup.lookup domain current bound counter nextPort tmp args) (StackClear.clear current))

noncomputable def costPolynomial (B : Polynomial Nat) (k : Nat) : Polynomial Nat :=
  StackLfpTables.costPolynomial B k + StackIndex.costPolynomial k + 14 * Polynomial.X ^ k + 11

theorem eval_costPolynomial (B : Polynomial Nat) (n k : Nat) :
    (costPolynomial B k).eval n = (StackLfpTables.costPolynomial B k).eval n +
      StackIndex.budget n k + 14 * n ^ k + 11 := by
  simp [costPolynomial, StackIndex.eval_costPolynomial]

set_option maxHeartbeats 800000 in
/-- The complete stack-restoring LFP evaluation constructor, given bounded
executions for its recursive body. Its Boolean result is membership in the
same rounds used by the verified semantic evaluator. -/
theorem evaluate_returns (s : EvalStore K Aux)
    (domain tmp rev current nextPort bound counter coord : K)
    (powerCounters : List K) (tupleSlots : List (K × K))
    (hsep : (domain :: tmp :: rev :: current :: nextPort :: bound :: counter :: coord ::
      (powerCounters ++ ports tupleSlots)).Nodup)
    (hempty : ∀ key, key ∈ tmp :: rev :: current :: nextPort :: bound :: counter :: coord ::
      (powerCounters ++ ports tupleSlots) → s.stk key = [])
    (hk : powerCounters.length = tupleSlots.length) (n B : Nat)
    (args : Fin tupleSlots.length → K) (values : Fin tupleSlots.length → Fin n)
    (hargs : ∀ i, args i ∉ [current, bound, counter, nextPort, tmp])
    (hvalues : ∀ i, s.stk (args i) = List.replicate (values i).val true)
    (p : TableEvaluation.Table n tupleSlots.length → (Fin tupleSlots.length → Fin n) → Bool)
    (body : EvalProgram K Aux) (hdomain : s.stk domain = List.replicate n true)
    (hbody : ∀ i, i < n ^ tupleSlots.length → ∀ R rem scratch,
      ∀ v : Fin tupleSlots.length → Fin n,
      ∀ remaining, remaining.length = tupleSlots.length → ∀ bits scratch',
      ∃ c, c ≤ B ∧ Returns body
        (packTuple (StackMaterialize.payload
          (running s current bound counter coord (@dense n tupleSlots.length)
            (n ^ tupleSlots.length) R i rem scratch) rev)
          tupleSlots bits (tupleValues v) remaining scratch') (p R v) c) :
    ∃ c, c ≤ (costPolynomial (Polynomial.C B) tupleSlots.length).eval n ∧
      Returns (evaluate domain tmp rev current nextPort bound counter coord powerCounters tupleSlots
        (List.ofFn args) body) s
        (decide (values ∈ TableEvaluation.rounds (DenseTables.next p) (n ^ tupleSlots.length))) c := by
  obtain ⟨a, ha, hp⟩ := StackSemanticRounds.semantic_rounds_executes s domain tmp rev current nextPort bound
    counter coord powerCounters tupleSlots hsep hempty hk n B p body hdomain hbody
  let R := TableEvaluation.rounds (DenseTables.next p) (n ^ tupleSlots.length)
  let t := setStack (result false s) current (dense R)
  have hcore := hsep
  simp only [List.nodup_cons, List.mem_cons, List.mem_append, not_or] at hcore
  have hlookup : [domain, current, bound, counter, nextPort, tmp].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true,
      not_or, and_true]
    tauto
  have ht (key : K) (hne : key ≠ current) : t.stk key = s.stk key := by
    simp [t, setStack, result, hne]
  obtain ⟨b, hb, hq⟩ := StackTableLookup.lookup_returns domain current bound counter nextPort tmp hlookup
    args values (fun v => decide (v ∈ R))
    (by
      intro i
      have h := hargs i
      simp only [List.mem_cons, List.not_mem_nil, not_false_eq_true, not_or, and_true] at h ⊢
      tauto) t
    (by rw [ht domain (by tauto)]; exact hdomain) (by simp [t, setStack, dense])
    (by
      intro i
      have hne : args i ≠ current := by
        have h := hargs i
        simp only [List.mem_cons, not_or] at h
        exact h.1
      rw [ht _ hne]
      exact hvalues i)
    (by rw [ht bound (by tauto)]; exact hempty bound (by simp))
    (by rw [ht counter (by tauto)]; exact hempty counter (by simp))
    (by rw [ht nextPort (by tauto)]; exact hempty nextPort (by simp))
    (by rw [ht tmp (by tauto)]; exact hempty tmp (by simp))
  have hclear := StackClear.clear_store current (result (decide (values ∈ R)) t)
  have hlen : (result (decide (values ∈ R)) t).stk current = dense R := by simp [result, t, setStack]
  rw [hlen, dense_length] at hclear
  have he : (⟨((result (decide (values ∈ R)) t).state.1, none),
      Function.update (result (decide (values ∈ R)) t).stk current []⟩ : EvalStore K Aux) =
      result (decide (values ∈ R)) s := by
    have hc : s.stk current = [] := hempty current (by simp)
    simp [result, t, setStack, Function.update_idem, ← hc]
  rw [he] at hclear
  refine ⟨a + (b + (2 * n ^ tupleSlots.length + 2)), ?_,
    Executes.seq hp (Executes.seq hq hclear)⟩
  rw [eval_costPolynomial]
  omega

end Lax979537Proofs.StackLfpValue
