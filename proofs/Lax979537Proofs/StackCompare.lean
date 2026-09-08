import Lax979537Proofs.StackClear

namespace Lax979537Proofs.StackCompare

open StackProgram StackTransfer

variable {K Aux : Type} [DecidableEq K]

def readPair (left right : K) : BitProgram K (Aux × Bool) :=
  .seq (.atom (.pop left (fun s b => ((s.1.1, b.isSome), s.2)))) (read right)

def scanLoop (left right : K) : BitProgram K (Aux × Bool) :=
  .loop (fun s => s.1.2 && s.2.isSome) (readPair left right)

def scan (left right : K) : BitProgram K (Aux × Bool) :=
  .seq (readPair left right) (scanLoop left right)

def less (left right : K) : BitProgram K (Aux × Bool) :=
  .seq (scan left right)
    (.seq (.atom (.load (fun s => ((s.1.1, !s.1.2 && s.2.isSome), none))))
      (.seq (StackClear.clear left) (StackClear.clear right)))

structure Residue where
  left : List Bool
  right : List Bool
  leftPresent : Bool
  rightHead : Option Bool

def residue : List Bool → List Bool → Residue
  | [], ys => ⟨[], ys.tail, false, ys.head?⟩
  | xs, [] => ⟨xs.tail, [], xs.head?.isSome, none⟩
  | _ :: xs, _ :: ys => residue xs ys

theorem residue_less (xs ys : List Bool) :
    (!(residue xs ys).leftPresent && (residue xs ys).rightHead.isSome) =
      decide (xs.length < ys.length) := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [residue]
  | cons b bs ih => cases ys <;> simp [residue, ih]

theorem residue_size (xs ys : List Bool) :
    (residue xs ys).left.length + (residue xs ys).right.length ≤ xs.length + ys.length := by
  induction xs generalizing ys with
  | nil => simp [residue, List.length_tail]
  | cons b bs ih =>
      cases ys with
      | nil => simp [residue]
      | cons c cs => have h := ih cs; simp only [residue, List.length_cons]; omega

theorem readPair_executes (base : K → List Bool) (left right : K) (hne : left ≠ right)
    (xs ys : List Bool) (a : Aux) (flag : Bool) (scratch : Option Bool) :
    Executes (readPair left right) (working base left right xs ys (a, flag) scratch)
      (working base left right xs.tail ys.tail (a, xs.head?.isSome) ys.head?) 2 := by
  have hp := Executes.atom
    (.pop left (fun s : (Aux × Bool) × Option Bool => fun b => ((s.1.1, b.isSome), s.2)))
    (working base left right xs ys (a, flag) scratch)
  have he : Op.apply
      (.pop left (fun s : (Aux × Bool) × Option Bool => fun b => ((s.1.1, b.isSome), s.2)))
      (working base left right xs ys (a, flag) scratch) =
      working base left right xs.tail ys (a, xs.head?.isSome) scratch := by
    apply Store.ext
    · simp [Op.apply, working, hne]
    · funext k
      by_cases hl : k = left <;> by_cases hr : k = right <;> simp_all [Op.apply, working]
  rw [he] at hp
  have hq := Executes.atom
    (.pop right (fun s : (Aux × Bool) × Option Bool => fun b => (s.1, b)))
    (working base left right xs.tail ys (a, xs.head?.isSome) scratch)
  have he' : Op.apply
      (.pop right (fun s : (Aux × Bool) × Option Bool => fun b => (s.1, b)))
      (working base left right xs.tail ys (a, xs.head?.isSome) scratch) =
      working base left right xs.tail ys.tail (a, xs.head?.isSome) ys.head? := by
    apply Store.ext
    · simp [Op.apply, working]
    · funext k
      by_cases hr : k = right <;> simp_all [Op.apply, working, Function.update_apply]
  rw [he'] at hq
  exact Executes.seq hp hq

theorem scanLoop_executes (base : K → List Bool) (left right : K) (hne : left ≠ right)
    (xs ys : List Bool) (a : Aux) :
    ∃ c, c ≤ 3 * (xs.length + ys.length) + 1 ∧
      Executes (scanLoop left right)
        (working base left right xs.tail ys.tail (a, xs.head?.isSome) ys.head?)
        (working base left right (residue xs ys).left (residue xs ys).right
          (a, (residue xs ys).leftPresent) (residue xs ys).rightHead) c := by
  induction xs generalizing ys with
  | nil => exact ⟨1, by omega, Executes.loop_false rfl⟩
  | cons b bs ih =>
      cases ys with
      | nil => exact ⟨1, by omega, Executes.loop_false rfl⟩
      | cons d ds =>
          obtain ⟨c, hc, hh⟩ := ih ds
          refine ⟨2 + c + 1, ?_, ?_⟩
          · simp only [List.length_cons]; omega
          · exact Executes.loop_true rfl
              (readPair_executes base left right hne bs ds a true (some d)) hh

theorem scan_executes (base : K → List Bool) (left right : K) (hne : left ≠ right)
    (xs ys : List Bool) (a : Aux) (flag : Bool) (scratch : Option Bool) :
    ∃ c, c ≤ 3 * (xs.length + ys.length) + 3 ∧
      Executes (scan left right) (working base left right xs ys (a, flag) scratch)
        (working base left right (residue xs ys).left (residue xs ys).right
          (a, (residue xs ys).leftPresent) (residue xs ys).rightHead) c := by
  obtain ⟨c, hc, hh⟩ := scanLoop_executes base left right hne xs ys a
  exact ⟨2 + c, by omega,
    Executes.seq (readPair_executes base left right hne xs ys a flag scratch) hh⟩

/-- Compare counter lengths, discard both counters, and preserve all other
stacks and the auxiliary control. The bit result is in the auxiliary register. -/
theorem less_executes (base : K → List Bool) (left right : K) (hne : left ≠ right)
    (xs ys : List Bool) (a : Aux) (flag : Bool) (scratch : Option Bool) :
    ∃ c, c ≤ 5 * (xs.length + ys.length) + 8 ∧
      Executes (less left right) (working base left right xs ys (a, flag) scratch)
        (working base left right [] [] (a, decide (xs.length < ys.length)) none) c := by
  obtain ⟨c, hc, hh⟩ := scan_executes base left right hne xs ys a flag scratch
  have hl := Executes.atom
    (.load (fun s : (Aux × Bool) × Option Bool => ((s.1.1, !s.1.2 && s.2.isSome), none)))
    (working base left right (residue xs ys).left (residue xs ys).right
      (a, (residue xs ys).leftPresent) (residue xs ys).rightHead)
  change Executes _ _ (working base left right (residue xs ys).left (residue xs ys).right
    (a, !(residue xs ys).leftPresent && (residue xs ys).rightHead.isSome) none) 1 at hl
  rw [residue_less] at hl
  have clearLeft (us vs : List Bool) (b : Aux × Bool) :
      Executes (StackClear.clear left) (working base left right us vs b none)
        (working base left right [] vs b none) (2 * us.length + 2) := by
    have h := StackClear.clear_store left (working base left right us vs b none)
    have he : (⟨(b, none), Function.update (working base left right us vs b none).stk left []⟩ :
        BitStore K (Aux × Bool)) = working base left right [] vs b none := by
      apply Store.ext
      · rfl
      · funext k
        by_cases hk : k = left
        · subst k; simp [working, hne]
        · by_cases hk' : k = right
          · subst k; simp [working, hk]
          · simp [working, hk, hk']
    change Executes _ _
      ⟨(b, none), Function.update (working base left right us vs b none).stk left []⟩ _ at h
    rw [he] at h
    simpa [working, hne] using h
  have clearRight (us vs : List Bool) (b : Aux × Bool) :
      Executes (StackClear.clear right) (working base left right us vs b none)
        (working base left right us [] b none) (2 * vs.length + 2) := by
    have h := StackClear.clear_store right (working base left right us vs b none)
    simpa [working, Function.update_idem] using h
  have h := Executes.seq hh (Executes.seq hl
    (Executes.seq (clearLeft (residue xs ys).left (residue xs ys).right _)
      (clearRight [] (residue xs ys).right _)))
  refine ⟨_, ?_, h⟩
  have hs := residue_size xs ys
  omega

end Lax979537Proofs.StackCompare
