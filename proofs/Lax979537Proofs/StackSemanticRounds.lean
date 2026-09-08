import Lax979537Proofs.DenseTables

namespace Lax979537Proofs.StackSemanticRounds

open StackProgram StackTransfer StackTuples StackBoolean StackTableStages DenseTables

variable {K Aux : Type} [DecidableEq K]

/-- The retained machine table is exactly the dense representation of the
rounds used by the existing semantic evaluator. The body contract uses
ordinary Fin-valued tuples, so it can be supplied by formula induction. -/
theorem semantic_rounds_executes (s : EvalStore K Aux)
    (domain tmp rev current nextPort bound counter coord : K)
    (powerCounters : List K) (tupleSlots : List (K × K))
    (hsep : (domain :: tmp :: rev :: current :: nextPort :: bound :: counter :: coord ::
      (powerCounters ++ ports tupleSlots)).Nodup)
    (hempty : ∀ key, key ∈ tmp :: rev :: current :: nextPort :: bound :: counter :: coord ::
      (powerCounters ++ ports tupleSlots) → s.stk key = [])
    (hk : powerCounters.length = tupleSlots.length) (n B : Nat)
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
    ∃ c, c ≤ (StackLfpTables.costPolynomial (Polynomial.C B) tupleSlots.length).eval n ∧
      Executes (StackLfpTables.run domain tmp rev current nextPort bound counter coord powerCounters tupleSlots body) s
        (setStack (result false s) current
          (dense (TableEvaluation.rounds (DenseTables.next p) (n ^ tupleSlots.length)))) c := by
  obtain ⟨c, hc, hp⟩ := StackLfpTables.run_executes s domain tmp rev current nextPort bound counter coord
    powerCounters tupleSlots hsep hempty hk (@dense n tupleSlots.length) (DenseTables.next p)
    (fun R => predicate (p R)) n B dense_length (dense_next p) body hdomain
    (by
      intro i hi R rem scratch values hlen hvalid remaining hrem bits scratch'
      obtain ⟨v, rfl⟩ := valid_values n tupleSlots.length values hlen hvalid
      simpa only [predicate_values] using hbody i hi R rem scratch v remaining hrem bits scratch')
    [] (dense_empty n tupleSlots.length)
  refine ⟨c, ?_, ?_⟩
  · simpa only [StackLfpTables.eval_costPolynomial, Polynomial.eval_C] using hc
  · simpa only [family, rounds_eq_iterate] using hp

end Lax979537Proofs.StackSemanticRounds
