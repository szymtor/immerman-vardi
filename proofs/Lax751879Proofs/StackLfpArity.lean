import Lax751879Proofs.StackLfpValue

namespace Lax751879Proofs.StackLfpArity

open StackProgram StackTransfer StackTuples StackBoolean StackTableStages DenseTables

variable {K Aux : Type} [DecidableEq K]

/-- The LFP constructor's arity is stated independently of its workspace
list, avoiding dependent casts when compiling a binder of arity k. -/
theorem evaluate_returns (s : EvalStore K Aux)
    (domain tmp rev current nextPort bound counter coord : K)
    (powerCounters : List K) (tupleSlots : List (K × K))
    (hsep : (domain :: tmp :: rev :: current :: nextPort :: bound :: counter :: coord ::
      (powerCounters ++ ports tupleSlots)).Nodup)
    (hempty : ∀ key, key ∈ tmp :: rev :: current :: nextPort :: bound :: counter :: coord ::
      (powerCounters ++ ports tupleSlots) → s.stk key = [])
    (k : Nat) (hslots : tupleSlots.length = k) (hk : powerCounters.length = k) (n B : Nat)
    (args : Fin k → K) (values : Fin k → Fin n)
    (hargs : ∀ i, args i ∉ [current, bound, counter, nextPort, tmp])
    (hvalues : ∀ i, s.stk (args i) = List.replicate (values i).val true)
    (p : TableEvaluation.Table n k → (Fin k → Fin n) → Bool)
    (body : EvalProgram K Aux) (hdomain : s.stk domain = List.replicate n true)
    (hbody : ∀ i, i < n ^ k → ∀ R rem scratch,
      ∀ v : Fin k → Fin n,
      ∀ remaining, remaining.length = k → ∀ bits scratch',
      ∃ c, c ≤ B ∧ Returns body
        (packTuple (StackMaterialize.payload
          (running s current bound counter coord (@dense n k)
            (n ^ k) R i rem scratch) rev)
          tupleSlots bits (tupleValues v) remaining scratch') (p R v) c) :
    ∃ c, c ≤ (StackLfpValue.costPolynomial (Polynomial.C B) k).eval n ∧
      Returns (StackLfpValue.evaluate domain tmp rev current nextPort bound counter coord powerCounters tupleSlots
        (List.ofFn args) body) s (decide (values ∈ TableEvaluation.rounds (DenseTables.next p) (n ^ k))) c := by
  subst k
  exact StackLfpValue.evaluate_returns s domain tmp rev current nextPort bound counter coord powerCounters
    tupleSlots hsep hempty hk n B args values hargs hvalues p body hdomain hbody

end Lax751879Proofs.StackLfpArity
