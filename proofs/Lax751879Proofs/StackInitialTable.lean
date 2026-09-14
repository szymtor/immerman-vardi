import Lax751879Proofs.StackMaterialize

namespace Lax751879Proofs.StackInitialTable

open StackProgram StackTransfer StackTuples StackBoolean

variable {K Aux : Type} [DecidableEq K]

def emptyTable (domain tmp rev current : K) (slots : List (K × K)) : EvalProgram K Aux :=
  StackMaterialize.materialize domain tmp rev current slots (answer false)

/-- The empty relation is stored as n^k false bits, including one bit at
arity zero. All temporary stacks are restored. -/
theorem initialize_executes (s : EvalStore K Aux) (domain tmp rev current : K)
    (slots : List (K × K)) (hsep : (domain :: tmp :: rev :: current :: ports slots).Nodup)
    (hempty : ∀ key, key ∈ tmp :: rev :: current :: ports slots → s.stk key = [])
    (n : Nat) (hdomain : s.stk domain = List.replicate n true) :
    ∃ c, c ≤ StackTuples.cost n 3 slots.length + 3 * n ^ slots.length + 3 ∧
      Executes (emptyTable domain tmp rev current slots) s
        (setStack (result false s) current (List.replicate (n ^ slots.length) false)) c := by
  obtain ⟨c, hc, hp⟩ := StackMaterialize.materialize_executes s domain tmp rev current slots hsep
    (by intro key hk; apply hempty key; simp only [List.mem_cons] at hk ⊢; tauto)
    (answer false) (fun _ => false) n 1 hdomain
    (by
      intro values hlen hvalid remaining hrem bits scratch
      exact ⟨1, le_rfl, answer_returns false _⟩)
  have htable : StackMaterialize.table n slots.length (fun _ => false) =
      List.replicate (n ^ slots.length) false := by simp [StackMaterialize.table, tuples_length]
  rw [htable, hempty current (by simp), List.append_nil] at hp
  exact ⟨c, hc, hp⟩

end Lax751879Proofs.StackInitialTable
