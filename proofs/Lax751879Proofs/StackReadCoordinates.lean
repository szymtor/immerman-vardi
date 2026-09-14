import Lax751879Proofs.StackCoordinate
import Lax751879Proofs.StackReadRelations

namespace Lax751879Proofs.StackReadCoordinates

open StackProgram StackTransfer StackReadRelations

variable {K Aux : Type} [DecidableEq K]

omit [DecidableEq K] in
theorem coordinate_separate (w : Workspace K) (coord : K) (hf : Fresh w coord) :
    [w.input, coord, w.domain, w.count, w.rev, w.tmp].Nodup := by
  have h := w.separate
  have h' := hf.1
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true,
    not_or, and_true] at h h' ⊢
  tauto

theorem coordinate_ready (w : Workspace K) (coord : K) (hf : Fresh w coord)
    (n : Nat) (s : BitStore K ((Aux × Bool) × Bool)) (hs : Ready w n s) :
    Ready w n (StackCoordinate.result w.input coord w.domain s) := by
  have h := w.separate
  have h' := hf.1
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true,
    not_or, and_true] at h h'
  have hp (key : K) (hi : key ≠ w.input) (hc : key ≠ coord) :
      (StackCoordinate.result w.input coord w.domain s).stk key = s.stk key :=
    StackCoordinate.result_preserves _ _ _ _ hi hc s
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hp _ (by tauto) (by tauto)]; exact hs.1
  · rw [hp _ (by tauto) (by tauto)]; exact hs.2.1
  · rw [hp _ (by tauto) (by tauto)]; exact hs.2.2.1
  · rw [hp _ (by tauto) (by tauto)]; exact hs.2.2.2.1
  · intro c hm
    have hcf := w.counter_fresh c hm
    simp only [List.mem_cons, List.not_mem_nil, not_false_eq_true, not_or, and_true] at hcf
    have hcc : c ≠ coord := fun he => hf.2 (he ▸ hm)
    rw [hp _ (by tauto) hcc]
    exact hs.2.2.2.2 c hm

theorem coordinate_input_le (w : Workspace K) (coord : K) (hf : Fresh w coord)
    (s : BitStore K ((Aux × Bool) × Bool)) :
    ((StackCoordinate.result w.input coord w.domain s).stk w.input).length ≤
      (s.stk w.input).length := by
  have hi : w.input ≠ coord := by
    have h := hf.1
    simp only [List.mem_cons, List.not_mem_nil, not_false_eq_true, not_or, and_true] at h
    tauto
  simpa [StackCoordinate.result, StackCheckBound.result, StackCheckedUnary.result, hi] using
    StackUnary.splitUnary_rest_le (s.stk w.input)

def readCoords (w : Workspace K) : List K → BitProgram K ((Aux × Bool) × Bool)
  | [] => .atom (.load (fun s => (s.1, none)))
  | c :: cs => .seq (StackCoordinate.parse w.input c w.domain w.count w.rev w.tmp) (readCoords w cs)

def result (w : Workspace K) : List K → BitStore K ((Aux × Bool) × Bool) → BitStore K ((Aux × Bool) × Bool)
  | [], s => ⟨(s.state.1, none), s.stk⟩
  | c :: cs, s => result w cs (StackCoordinate.result w.input c w.domain s)

theorem readCoords_executes (w : Workspace K) (coords : List K) (hn : coords.Nodup)
    (hf : ∀ c ∈ coords, Fresh w c) (n : Nat) (s : BitStore K ((Aux × Bool) × Bool))
    (hs : Ready w n s) (he : ∀ c ∈ coords, s.stk c = []) :
    ∃ t, t ≤ coords.length * (15 * (s.stk w.input).length + 12 * n + 21) + 1 ∧
      Executes (readCoords w coords) s (result w coords s) t := by
  induction coords generalizing s with
  | nil => exact ⟨1, by simp, Executes.atom _ _⟩
  | cons c cs ih =>
      obtain ⟨hnot, hn'⟩ := List.nodup_cons.mp hn
      have hfc := hf c (by simp)
      obtain ⟨a, ha, hp⟩ := StackCoordinate.parse_executes w.input c w.domain w.count w.rev w.tmp
        (coordinate_separate w c hfc) s (he c (by simp)) hs.2.2.1 hs.2.2.2.1 hs.2.1
      rw [hs.1, List.length_replicate] at ha
      let u := StackCoordinate.result w.input c w.domain s
      have hu := coordinate_ready w c hfc n s hs
      have hrest : ∀ d ∈ cs, u.stk d = [] := by
        intro d hm
        have hfd := (hf d (by simp [hm])).1
        simp only [List.mem_cons, List.not_mem_nil, not_false_eq_true, not_or, and_true] at hfd
        have hdc : d ≠ c := fun heq => hnot (heq ▸ hm)
        rw [StackCoordinate.result_preserves w.input c w.domain d (by tauto) hdc]
        exact he d (by simp [hm])
      obtain ⟨b, hb, hq⟩ := ih hn' (fun d hm => hf d (by simp [hm])) u hu hrest
      have hlen := coordinate_input_le w c hfc s
      change (u.stk w.input).length ≤ (s.stk w.input).length at hlen
      have hmul := Nat.mul_le_mul_left cs.length
        (show 15 * (u.stk w.input).length + 12 * n + 21 ≤
          15 * (s.stk w.input).length + 12 * n + 21 from by omega)
      refine ⟨a + b, ?_, Executes.seq hp hq⟩
      rw [List.length_cons, Nat.succ_mul]
      omega

theorem result_preserves (w : Workspace K) (coords : List K) (key : K)
    (hi : key ≠ w.input) (hc : key ∉ coords) (s : BitStore K ((Aux × Bool) × Bool)) :
    (result w coords s).stk key = s.stk key := by
  induction coords generalizing s with
  | nil => rfl
  | cons c cs ih =>
      have h : key ≠ c ∧ key ∉ cs := by simpa using hc
      rw [result, ih h.2]
      exact StackCoordinate.result_preserves _ _ _ _ hi h.1 s

theorem input_length_le (w : Workspace K) (coords : List K)
    (hf : ∀ c ∈ coords, Fresh w c) (s : BitStore K ((Aux × Bool) × Bool)) :
    ((result w coords s).stk w.input).length ≤ (s.stk w.input).length := by
  induction coords generalizing s with
  | nil => exact le_refl _
  | cons c cs ih =>
      exact (ih (fun d hm => hf d (by simp [hm])) _).trans
        (coordinate_input_le w c (hf c (by simp)) s)

theorem coords_ready (w : Workspace K) (coords : List K) (hf : ∀ c ∈ coords, Fresh w c)
    (n : Nat) (s : BitStore K ((Aux × Bool) × Bool)) (hs : Ready w n s) :
    Ready w n (result w coords s) := by
  induction coords generalizing s with
  | nil => exact hs
  | cons c cs ih =>
      exact ih (fun d hm => hf d (by simp [hm])) _ (coordinate_ready w c (hf c (by simp)) n s hs)

end Lax751879Proofs.StackReadCoordinates
