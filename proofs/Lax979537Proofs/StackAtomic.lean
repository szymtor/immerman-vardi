import Lax979537Proofs.StackBoolean
import Lax979537Proofs.StackCheckBound

namespace Lax979537Proofs.StackAtomic

open StackProgram StackTransfer StackBoolean

variable {K Aux : Type} [DecidableEq K]

def less (left right copyLeft copyRight tmp : K) : EvalProgram K Aux :=
  .seq (answer true) (StackCheckBound.checkBound left right copyLeft copyRight tmp)

def equal (left right copyLeft copyRight tmp savedPort : K) : EvalProgram K Aux :=
  .seq (binary savedPort (· || ·) (less left right copyLeft copyRight tmp)
    (less right left copyLeft copyRight tmp)) negate

theorem less_returns (left right copyLeft copyRight tmp : K)
    (hsep : [left, right, copyLeft, copyRight, tmp].Nodup) (s : EvalStore K Aux)
    (hl : s.stk copyLeft = []) (hr : s.stk copyRight = []) (ht : s.stk tmp = []) :
    ∃ cost, cost ≤ 12 * ((s.stk left).length + (s.stk right).length) + 19 ∧
      Returns (less left right copyLeft copyRight tmp) s
        (decide ((s.stk left).length < (s.stk right).length)) cost := by
  obtain ⟨c, hc, h⟩ := StackCheckBound.checkBound_executes left right copyLeft copyRight tmp
    hsep (result true s) hl hr ht
  have hx := Executes.seq (answer_returns true s) h
  change c ≤ 12 * ((s.stk left).length + (s.stk right).length) + 18 at hc
  refine ⟨1 + c, by omega, ?_⟩
  simpa [less, Returns, StackCheckBound.result, result] using hx

theorem not_less_both (a b : Nat) : (!(decide (a < b) || decide (b < a))) = decide (a = b) := by
  by_cases h : a = b
  · subst b; simp
  · rcases lt_or_gt_of_ne h with hlt | hlt <;> simp [h, hlt]

/-- Equality and order compare lengths of unary counters. Input counters,
unrelated stacks, and the saved-result stack are all restored on return. -/
theorem equal_returns (left right copyLeft copyRight tmp savedPort : K)
    (hsep : [left, right, copyLeft, copyRight, tmp, savedPort].Nodup) (s : EvalStore K Aux)
    (hl : s.stk copyLeft = []) (hr : s.stk copyRight = []) (ht : s.stk tmp = []) :
    ∃ cost, cost ≤ 24 * ((s.stk left).length + (s.stk right).length) + 41 ∧
      Returns (equal left right copyLeft copyRight tmp savedPort) s
        (decide ((s.stk left).length = (s.stk right).length)) cost := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true,
    not_or, and_true] at hsep
  have h1 : [left, right, copyLeft, copyRight, tmp].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true, not_or, and_true]
    tauto
  have h2 : [right, left, copyLeft, copyRight, tmp].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true, not_or, and_true]
    tauto
  obtain ⟨a, ha, hp⟩ := less_returns left right copyLeft copyRight tmp h1 s hl hr ht
  let b := decide ((s.stk left).length < (s.stk right).length)
  have hf (key : K) (hne : key ≠ savedPort) : (saved savedPort b s).stk key = s.stk key := by
    simp [saved, hne]
  obtain ⟨c, hc, hq⟩ := less_returns right left copyLeft copyRight tmp h2 (saved savedPort b s)
    (by rw [hf _ (by tauto)]; exact hl)
    (by rw [hf _ (by tauto)]; exact hr)
    (by rw [hf _ (by tauto)]; exact ht)
  rw [hf right (by tauto), hf left (by tauto)] at hc hq
  have hh := negate_returns (binary_returns savedPort (· || ·) hp hq)
  rw [not_less_both] at hh
  exact ⟨a + c + 2 + 1, by omega, hh⟩

/-- Port equality is decided when compiling the fixed syntax, so repeated
variables such as x = x require no dynamic counter comparison. -/
def equalValue (left right copyLeft copyRight tmp savedPort : K) : EvalProgram K Aux :=
  if left = right then answer true else equal left right copyLeft copyRight tmp savedPort

def lessValue (left right copyLeft copyRight tmp : K) : EvalProgram K Aux :=
  if left = right then answer false else less left right copyLeft copyRight tmp

theorem equalValue_returns (left right copyLeft copyRight tmp savedPort : K)
    (hwork : [copyLeft, copyRight, tmp, savedPort].Nodup)
    (hlfresh : left ∉ [copyLeft, copyRight, tmp, savedPort])
    (hrfresh : right ∉ [copyLeft, copyRight, tmp, savedPort])
    (s : EvalStore K Aux) (hl : s.stk copyLeft = []) (hr : s.stk copyRight = [])
    (ht : s.stk tmp = []) :
    ∃ cost, cost ≤ 24 * ((s.stk left).length + (s.stk right).length) + 41 ∧
      Returns (equalValue left right copyLeft copyRight tmp savedPort) s
        (decide ((s.stk left).length = (s.stk right).length)) cost := by
  by_cases he : left = right
  · subst right
    exact ⟨1, by omega, by simpa [equalValue] using answer_returns true s⟩
  · simpa only [equalValue, if_neg he] using equal_returns left right copyLeft copyRight tmp
      savedPort (by simpa [List.nodup_cons, he, hlfresh, hrfresh] using hwork) s hl hr ht

theorem lessValue_returns (left right copyLeft copyRight tmp : K)
    (hwork : [copyLeft, copyRight, tmp].Nodup)
    (hlfresh : left ∉ [copyLeft, copyRight, tmp])
    (hrfresh : right ∉ [copyLeft, copyRight, tmp])
    (s : EvalStore K Aux) (hl : s.stk copyLeft = []) (hr : s.stk copyRight = [])
    (ht : s.stk tmp = []) :
    ∃ cost, cost ≤ 12 * ((s.stk left).length + (s.stk right).length) + 19 ∧
      Returns (lessValue left right copyLeft copyRight tmp) s
        (decide ((s.stk left).length < (s.stk right).length)) cost := by
  by_cases he : left = right
  · subst right
    exact ⟨1, by omega, by simpa [lessValue] using answer_returns false s⟩
  · simpa only [lessValue, if_neg he] using less_returns left right copyLeft copyRight tmp
      (by simpa [List.nodup_cons, he, hlfresh, hrfresh] using hwork) s hl hr ht

end Lax979537Proofs.StackAtomic
