import Lax751879Proofs.StackStages
import Lax751879Proofs.StackTableRound

namespace Lax751879Proofs.StackTableStages

open StackProgram StackTransfer StackFor StackTuples StackBoolean StackStages

variable {K Aux α : Type} [DecidableEq K]

def family (s : EvalStore K Aux) (current : K) (encode : α → List Bool) (a : α) : EvalStore K Aux :=
  setStack (result false s) current (encode a)

def running (s : EvalStore K Aux) (current bound counter coord : K)
    (encode : α → List Bool) (m : Nat) (a : α) (i remaining : Nat) (scratch : Option Bool) :
    EvalStore K Aux :=
  pack (prepared (family s current encode) bound m) counter coord a i remaining scratch

def tableStages (domain tmp rev current next bound counter coord : K)
    (powerCounters : List K) (tupleSlots : List (K × K)) (body : EvalProgram K Aux) : EvalProgram K Aux :=
  stages domain bound counter coord tmp powerCounters
    (StackTableRound.round domain tmp rev current next tupleSlots body)

def roundCost (n k B : Nat) : Nat := StackTuples.cost n (B + 2) k + 11 * n ^ k + 9

noncomputable def costPolynomial (B : Polynomial Nat) (k : Nat) : Polynomial Nat :=
  StackStages.costPolynomial
    (StackTuples.costPolynomial (B + 2) k + 11 * Polynomial.X ^ k + 9) k

theorem eval_costPolynomial (B : Polynomial Nat) (n k : Nat) :
    (costPolynomial B k).eval n = StackPower.cost k n + (roundCost n k (B.eval n) + 14) * n ^ k + 10 := by
  simp [costPolynomial, StackStages.eval_costPolynomial, StackTuples.eval_costPolynomial, roundCost]

set_option maxHeartbeats 800000 in
/-- Iterate a represented table transformer exactly n^k times. The body
premise is a bounded Boolean evaluation for each valid tuple in each old
table; it does not assume executions or correctness of the stage loop. -/
theorem tableStages_executes (s : EvalStore K Aux)
    (domain tmp rev current next bound counter coord : K)
    (powerCounters : List K) (tupleSlots : List (K × K))
    (hsep : (domain :: tmp :: rev :: current :: next :: bound :: counter :: coord ::
      (powerCounters ++ ports tupleSlots)).Nodup)
    (hempty : ∀ key, key ∈ tmp :: rev :: next :: bound :: counter :: coord ::
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
    (a : α) : ∃ c, c ≤ StackPower.cost tupleSlots.length n +
        (roundCost n tupleSlots.length B + 14) * n ^ tupleSlots.length + 10 ∧
      Executes (tableStages domain tmp rev current next bound counter coord powerCounters tupleSlots body)
        (family s current encode a) (family s current encode ((step^[n ^ tupleSlots.length]) a)) c := by
  have hcore := hsep
  simp only [List.nodup_cons, List.mem_cons, List.mem_append, not_or] at hcore
  have hstage : [domain, bound, counter, coord, tmp].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true,
      not_or, and_true]
    tauto
  have hround : (domain :: tmp :: rev :: current :: next :: ports tupleSlots).Nodup := by
    simp only [List.nodup_cons, List.mem_cons, not_or]
    have htail := hcore
    simp only [List.nodup_append] at htail
    tauto
  have hpool : powerCounters.Nodup := by
    simp only [List.nodup_append] at hcore
    tauto
  have hpoolFresh : ∀ key ∈ powerCounters, key ∉ [domain, bound, counter, coord, tmp] := by
    intro key hm
    simp only [List.mem_cons, List.not_mem_nil, not_false_eq_true, not_or, and_true]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro he <;> subst key <;> tauto
  have hcur (key : K) (hm : key ∈ [bound, counter, coord, tmp] ++ powerCounters) : key ≠ current := by
    intro he
    subst key
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm
    tauto
  have hrun (key : K) (hm : key ∈ domain :: tmp :: rev :: next :: ports tupleSlots)
      (a : α) (i rem : Nat) (scratch : Option Bool) :
      (running s current bound counter coord encode (n ^ tupleSlots.length) a i rem scratch).stk key =
        s.stk key := by
    have hne : key ≠ coord ∧ key ≠ counter ∧ key ≠ bound ∧ key ≠ current := by
      simp only [List.mem_cons] at hm
      rcases hm with rfl | rfl | rfl | rfl | hm
      · tauto
      · tauto
      · tauto
      · tauto
      · refine ⟨?_, ?_, ?_, ?_⟩ <;> intro he <;> subst key <;> tauto
    simp [running, pack, working, prepared, family, setStack, result, hne.1, hne.2.1,
      hne.2.2.1, hne.2.2.2]
  obtain ⟨c, hc, hp⟩ := stages_executes (family s current encode) domain bound counter coord tmp
    hstage powerCounters hpool hpoolFresh
    (by
      intro a key hm
      simp only [family, setStack, result, Function.update_of_ne (hcur key hm)]
      apply hempty key
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
      tauto)
    (StackTableRound.round domain tmp rev current next tupleSlots body) step n
    (roundCost n tupleSlots.length B)
    (by
      intro i hi a rem scratch
      rw [hk] at hi
      let u := running s current bound counter coord encode (n ^ tupleSlots.length) a i rem scratch
      obtain ⟨c, hc, hp⟩ := StackTableRound.round_executes u domain tmp rev current next tupleSlots hround
        (by
          intro key hm
          rw [hrun key (by simp only [List.mem_cons] at hm ⊢; tauto)]
          apply hempty key
          simp only [List.mem_cons, List.mem_append] at hm ⊢
          tauto)
        body (b a) n B (by rw [hrun domain (by simp)]; exact hdomain)
        (hbody i hi a rem scratch)
      have hulen : u.stk current = encode a := by
        have hne : current ≠ coord ∧ current ≠ counter ∧ current ≠ bound := by tauto
        simp [u, running, pack, working, prepared, family, setStack, hne.1, hne.2.1, hne.2.2]
      rw [hulen, hlength] at hc
      have he : setStack (result false u) current (StackMaterialize.table n tupleSlots.length (b a)) =
          running s current bound counter coord encode (n ^ tupleSlots.length) (step a) i rem none := by
        apply Store.ext
        · rfl
        · funext key
          by_cases he : key = current
          · subst key
            have hne : current ≠ coord ∧ current ≠ counter ∧ current ≠ bound := by tauto
            simp [u, running, pack, working, prepared, family, setStack, result,
              hne.1, hne.2.1, hne.2.2, hstep]
          · simp [u, running, pack, working, prepared, family, setStack, result,
              Function.update_apply, he]
      rw [he] at hp
      refine ⟨c, none, ?_, ?_⟩
      · dsimp only [roundCost]; omega
      · simpa only [hk] using hp)
    a (by
      have hdc : domain ≠ current := by tauto
      simpa [family, setStack, result, hdc] using hdomain)
  simpa only [hk] using (show ∃ c, c ≤ StackPower.cost powerCounters.length n +
      (roundCost n tupleSlots.length B + 14) * n ^ powerCounters.length + 10 ∧
      Executes (tableStages domain tmp rev current next bound counter coord powerCounters tupleSlots body)
        (family s current encode a) (family s current encode ((step^[n ^ powerCounters.length]) a)) c from
    ⟨c, hc, hp⟩)

end Lax751879Proofs.StackTableStages
