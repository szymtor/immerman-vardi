import Lax751879Proofs.StackUnary

namespace Lax751879Proofs.StackCheckedUnary

open StackProgram StackTransfer

variable {K Aux : Type} [DecidableEq K]

def recordSuccess : BitProgram K (Aux × Bool) :=
  .atom (.load (fun s => ((s.1.1, s.1.2 && s.2.isSome), none)))

def parse (src counter : K) : BitProgram K (Aux × Bool) :=
  .seq (StackUnary.parse src counter) recordSuccess

def result (src counter : K) (s : BitStore K (Aux × Bool)) : BitStore K (Aux × Bool) :=
  let r := StackUnary.splitUnary (s.stk src)
  ⟨((s.state.1.1, s.state.1.2 && r.2.isSome), none),
    Function.update (Function.update s.stk src (r.2.getD [])) counter
      (List.replicate r.1 true ++ s.stk counter)⟩

theorem parse_executes (src counter : K) (hne : src ≠ counter) (s : BitStore K (Aux × Bool)) :
    Executes (parse src counter) s (result src counter s)
      (3 * (StackUnary.splitUnary (s.stk src)).1 + 3) := by
  have h := StackUnary.parse_executes s.stk src counter hne
    (s.stk src) (s.stk counter) s.state.1 s.state.2
  simp only [working, Function.update_eq_self, Prod.mk.eta] at h
  have hl := Executes.atom
    (.load (fun q : (Aux × Bool) × Option Bool => ((q.1.1, q.1.2 && q.2.isSome), none)))
    (⟨(s.state.1, StackUnary.finished (StackUnary.splitUnary (s.stk src)).2),
      Function.update (Function.update s.stk src ((StackUnary.splitUnary (s.stk src)).2.getD []))
        counter (List.replicate (StackUnary.splitUnary (s.stk src)).1 true ++ s.stk counter)⟩ :
      BitStore K (Aux × Bool))
  have hh := Executes.seq h hl
  have he : (StackUnary.finished (StackUnary.splitUnary (s.stk src)).2).isSome =
      (StackUnary.splitUnary (s.stk src)).2.isSome := by simp [StackUnary.finished]
  have ht : (3 * (StackUnary.splitUnary (s.stk src)).1 + 2) + 1 =
      3 * (StackUnary.splitUnary (s.stk src)).1 + 3 := by omega
  simpa only [parse, recordSuccess, result, Op.apply, he, ht] using hh

theorem parse_linear_bound (src counter : K) (hne : src ≠ counter)
    (s : BitStore K (Aux × Bool)) :
    ∃ t, t ≤ 3 * (s.stk src).length + 3 ∧ Executes (parse src counter) s (result src counter s) t := by
  refine ⟨_, ?_, parse_executes src counter hne s⟩
  have h := StackUnary.splitUnary_le (s.stk src)
  omega

theorem result_preserves (src counter key : K) (hs : key ≠ src) (hc : key ≠ counter)
    (s : BitStore K (Aux × Bool)) : (result src counter s).stk key = s.stk key := by
  simp [result, hs, hc]

/-- Reject trailing data without consuming it. -/
def checkEnd (src : K) : BitProgram K (Aux × Bool) :=
  .atom (.peek src (fun s b => ((s.1.1, s.1.2 && b.isNone), none)))

theorem checkEnd_executes (src : K) (s : BitStore K (Aux × Bool)) :
    Executes (checkEnd src) s
      ⟨((s.state.1.1, s.state.1.2 && decide (s.stk src = [])), none), s.stk⟩ 1 := by
  have h := Executes.atom
    (.peek src (fun q : (Aux × Bool) × Option Bool => fun b => ((q.1.1, q.1.2 && b.isNone), none))) s
  have he : (s.stk src).head?.isNone = decide (s.stk src = []) := by
    cases s.stk src <;> rfl
  simpa only [checkEnd, Op.apply, he] using h

end Lax751879Proofs.StackCheckedUnary
