import Lax979537Proofs.StackPower

namespace Lax979537Proofs.StackHorner

open StackProgram StackTransfer StackRepeat

variable {K Aux : Type} [DecidableEq K]

/-- One unary Horner step: index := domain-size * index + coordinate.
The domain size and coordinate are read from their preserved stacks. -/
def step (domain index counter tmp coord : K) : BitProgram K Aux :=
  .seq (transfer index counter)
    (.seq (repeatCount counter (StackCopy.copy domain index tmp)) (StackCopy.copy coord index tmp))

def setIndex (s : BitStore K Aux) (index : K) (a : Nat) : BitStore K Aux :=
  ⟨(s.state.1, none), Function.update s.stk index (List.replicate a true)⟩

theorem step_executes (domain index counter tmp coord : K)
    (hsep : [domain, index, counter, tmp].Nodup) (hcoord : coord ∉ [index, counter, tmp])
    (n a v : Nat) (s : BitStore K Aux)
    (hdomain : s.stk domain = List.replicate n true)
    (hindex : s.stk index = List.replicate a true) (hvalue : s.stk coord = List.replicate v true)
    (hcounter : s.stk counter = []) (htmp : s.stk tmp = []) :
    ∃ c, c ≤ (7 * n + 9) * a + 7 * v + 8 ∧
      Executes (step domain index counter tmp coord) s (setIndex s index (n * a + v)) c := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true,
    not_or, and_true] at hsep
  simp only [List.mem_cons, List.not_mem_nil, not_false_eq_true, not_or, and_true] at hcoord
  have hdi : domain ≠ index := by tauto
  have hdc : domain ≠ counter := by tauto
  have hdt : domain ≠ tmp := by tauto
  have hic : index ≠ counter := by tauto
  have hit : index ≠ tmp := by tauto
  have hct : counter ≠ tmp := by tauto
  let u := working s.stk counter index (List.replicate a true) [] s.state.1 none
  have hmove := transfer_store index counter hic s
  rw [hindex, hcounter, List.reverse_replicate, List.append_nil, List.length_replicate] at hmove
  have hu : (⟨(s.state.1, none), Function.update (Function.update s.stk index []) counter
      (List.replicate a true)⟩ : BitStore K Aux) = u := by
    apply Store.ext
    · rfl
    · funext key
      by_cases hk : key = index <;> simp_all [u, working, Function.update_apply]
  rw [hu] at hmove
  let Valid : BitStore K Aux → Prop := fun q =>
    q.stk domain = List.replicate n true ∧ q.stk tmp = []
  have hread : ∀ q, Valid q → Valid (readStore counter q) := by
    intro q hq
    simpa [Valid, readStore, Op.apply, hdc, Ne.symm hct] using hq
  have hf : ∀ q, Valid q → Valid (StackPower.addTokens index n q) := by
    intro q hq
    simpa [Valid, StackPower.addTokens, hdi, Ne.symm hit] using hq
  have hframe : ∀ q, Valid q → (StackPower.addTokens index n q).stk counter = q.stk counter := by
    intro q _
    simp [StackPower.addTokens, Ne.symm hic]
  have hbody : ∀ q, Valid q → ∃ c, c ≤ 7 * n + 4 ∧
      Executes (StackCopy.copy domain index tmp) q (StackPower.addTokens index n q) c := by
    intro q hq
    have hp := StackCopy.copy_store domain index tmp hdi hdt hit q hq.2
    rw [hq.1, List.length_replicate] at hp
    exact ⟨7 * n + 4, le_rfl, hp⟩
  obtain ⟨c, hc, hp⟩ := repeat_executes counter (StackCopy.copy domain index tmp)
    (StackPower.addTokens index n) Valid (7 * n + 4) hread hf hframe hbody u
    (by simp [Valid, u, working, hdc, hdi, Ne.symm hct, Ne.symm hit, hdomain, htmp])
  have hlen : (u.stk counter).length = a := by simp [u, working, Ne.symm hic]
  rw [hlen] at hc hp
  have hresult := StackPower.result_addTokens s.stk counter index (Ne.symm hic)
    (List.replicate a true) [] s.state.1 none n
  simp only [List.length_replicate, List.append_nil] at hresult
  rw [hresult] at hp
  have he : working s.stk counter index [] (List.replicate (n * a) true) s.state.1 none =
      setIndex s index (n * a) := by simp [working, setIndex, ← hcounter]
  rw [he] at hp
  have hcopy := StackCopy.copy_store coord index tmp hcoord.1 hcoord.2.2 hit
    (setIndex s index (n * a)) (by simp [setIndex, Ne.symm hit, htmp])
  have hvalue' : (setIndex s index (n * a)).stk coord = List.replicate v true := by
    simp [setIndex, hcoord.1, hvalue]
  rw [hvalue', List.length_replicate] at hcopy
  have he' : (⟨((setIndex s index (n * a)).state.1, none),
      Function.update (setIndex s index (n * a)).stk index
        (List.replicate v true ++ (setIndex s index (n * a)).stk index)⟩ : BitStore K Aux) =
      setIndex s index (n * a + v) := by
    simp [setIndex, Function.update_idem, Nat.add_comm]
  rw [he'] at hcopy
  refine ⟨(3 * a + 2) + (c + (7 * v + 4)), ?_, Executes.seq hmove (Executes.seq hp hcopy)⟩
  simp only [Nat.add_mul] at hc ⊢
  omega

end Lax979537Proofs.StackHorner
