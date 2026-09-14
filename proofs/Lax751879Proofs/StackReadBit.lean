import Lax751879Proofs.StackLookup
import Lax751879Proofs.StackBoolean
import Lax751879Proofs.StackClear
import Lax751879Proofs.StackTuples

namespace Lax751879Proofs.StackReadBit

open StackProgram StackTransfer StackBoolean StackTuples

variable {K Aux : Type} [DecidableEq K]

def popAnswer (buffer : K) : EvalProgram K Aux :=
  .atom (.pop buffer (fun s b => (((s.1.1.1, true), b.getD false), none)))

def readBit (table index buffer tmp : K) : EvalProgram K Aux :=
  .seq (StackCopy.copy table buffer tmp)
    (.seq (StackRepeat.repeatCount index (StackLookup.discard buffer))
      (.seq (popAnswer buffer) (StackClear.clear buffer)))

/-- Read a bit at a unary index without changing the source table. The
index is consumed and all copy workspace is cleared. Out-of-range indices
return false, so the routine is total independently of the caller's bounds. -/
theorem readBit_executes (table index buffer tmp : K)
    (hsep : [table, index, buffer, tmp].Nodup) (s : EvalStore K Aux)
    (hb : s.stk buffer = []) (ht : s.stk tmp = []) :
    ∃ c, c ≤ 9 * (s.stk table).length + 3 * (s.stk index).length + 9 ∧
      Executes (readBit table index buffer tmp) s
        (setStack (result ((s.stk table)[(s.stk index).length]?.getD false) s) index []) c := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true,
    not_or, and_true] at hsep
  have htb : table ≠ buffer := by tauto
  have htt : table ≠ tmp := by tauto
  have hbt : buffer ≠ tmp := by tauto
  have hib : index ≠ buffer := by tauto
  have hcopy := StackCopy.copy_store table buffer tmp htb htt hbt s ht
  rw [hb, List.append_nil] at hcopy
  have he : (⟨(s.state.1, none), Function.update s.stk buffer (s.stk table)⟩ : EvalStore K Aux) =
      working s.stk index buffer (s.stk index) (s.stk table) s.state.1 none := by
    simp [working]
  rw [he] at hcopy
  obtain ⟨c, hc, hskip⟩ := StackLookup.skip_executes s.stk index buffer hib
    (s.stk index) (s.stk table) s.state.1 none
  let u := working s.stk index buffer [] ((s.stk table).drop (s.stk index).length) s.state.1 none
  let bit := (s.stk table)[(s.stk index).length]?.getD false
  let v := working s.stk index buffer [] ((s.stk table).drop ((s.stk index).length + 1))
    ((s.state.1.1.1, true), bit) none
  have hpop := Executes.atom (.pop buffer
    (fun q : ((Aux × Bool) × Bool) × Option Bool => fun b => (((q.1.1.1, true), b.getD false), none))) u
  have he' : Op.apply (.pop buffer
      (fun q : ((Aux × Bool) × Bool) × Option Bool => fun b => (((q.1.1.1, true), b.getD false), none))) u = v := by
    apply Store.ext
    · simp [u, v, Op.apply, working, bit]
    · funext key
      by_cases hk : key = buffer
      · subst key; simp [u, v, Op.apply, working, List.tail_drop]
      · simp [u, v, Op.apply, working, hk]
  rw [he'] at hpop
  have hclear := StackClear.clear_store buffer v
  have hv : v.stk buffer = (s.stk table).drop ((s.stk index).length + 1) := by simp [v, working]
  rw [hv] at hclear
  have he'' : (⟨(v.state.1, none), Function.update v.stk buffer []⟩ : EvalStore K Aux) =
      setStack (result bit s) index [] := by
    apply Store.ext
    · rfl
    · funext key
      by_cases hk : key = buffer
      · subst key; simp [v, working, setStack, result, Ne.symm hib, hb]
      · simp [v, working, setStack, result, hk]
  rw [he''] at hclear
  refine ⟨(7 * (s.stk table).length + 4) +
    (c + (1 + (2 * ((s.stk table).drop ((s.stk index).length + 1)).length + 2))), ?_,
      Executes.seq hcopy (Executes.seq hskip (Executes.seq hpop hclear))⟩
  simp only [List.length_drop]
  omega

end Lax751879Proofs.StackReadBit
