import Lax751879Proofs.StackRepeat

namespace Lax751879Proofs.StackTake

open StackProgram StackTransfer StackRepeat StackCopy

variable {K Aux : Type} [DecidableEq K]

/-- Fixed-length prefix, padding exhaustion with false. Padding keeps the
machine total; a separate sticky validity bit records insufficient input. -/
def paddedPrefix : Nat → List Bool → List Bool
  | 0, _ => []
  | n + 1, xs => xs.head?.getD false :: paddedPrefix n xs.tail

@[simp] theorem prefix_length (n : Nat) (xs : List Bool) : (paddedPrefix n xs).length = n := by
  induction n generalizing xs <;> simp [paddedPrefix, *]

theorem prefix_eq_take (n : Nat) (xs : List Bool) (h : n ≤ xs.length) :
    paddedPrefix n xs = xs.take n := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih =>
      cases xs with
      | nil => simp at h
      | cons b bs => simp only [paddedPrefix, List.head?_cons, Option.getD_some,
          List.tail_cons, List.take_succ_cons]; rw [ih bs (by simpa using h)]

theorem enough_succ (n : Nat) (xs : List Bool) :
    (xs.head?.isSome && decide (n ≤ xs.tail.length)) = decide (n + 1 ≤ xs.length) := by
  cases xs <;> simp <;> rfl

def body (src dst : K) : BitProgram K (Aux × Bool) :=
  .seq (.atom (.pop src (fun s b => ((s.1.1, s.1.2 && b.isSome), b))))
    (.atom (.push dst (fun s => s.2.getD false)))

def bodyStore (src dst : K) (s : BitStore K (Aux × Bool)) : BitStore K (Aux × Bool) :=
  Op.apply (.push dst (fun s => s.2.getD false))
    (Op.apply (.pop src (fun s b => ((s.1.1, s.1.2 && b.isSome), b))) s)

/-- Extract a counted prefix in reverse order. The caller can transfer it
once more to put a dense relation table into canonical order. -/
def takeBits (counter src dst : K) : BitProgram K (Aux × Bool) :=
  repeatCount counter (body src dst)

theorem body_executes (src dst : K) (s : BitStore K (Aux × Bool)) :
    Executes (body src dst) s (bodyStore src dst s) 2 :=
  Executes.seq (Executes.atom _ _) (Executes.atom _ _)

theorem body_working (base : K → List Bool) (counter src dst : K) (hsd : src ≠ dst)
    (xs ys zs : List Bool) (a : Aux) (valid : Bool) (scratch : Option Bool) :
    bodyStore src dst (working3 base counter src dst xs ys zs (a, valid) scratch) =
      working3 base counter src dst xs ys.tail (ys.head?.getD false :: zs)
        (a, valid && ys.head?.isSome) ys.head? := by
  apply Store.ext
  · simp [bodyStore, Op.apply, working3, hsd]
  · funext k
    by_cases hs : k = src <;> by_cases hd : k = dst <;>
      simp_all [bodyStore, Op.apply, working3]

theorem result_working (base : K → List Bool) (counter src dst : K)
    (hcs : counter ≠ src) (hcd : counter ≠ dst) (hsd : src ≠ dst)
    (xs ys zs : List Bool) (a : Aux) (valid : Bool) (scratch : Option Bool) :
    result counter (bodyStore src dst) xs.length
      (working3 base counter src dst xs ys zs (a, valid) scratch) =
      working3 base counter src dst [] (ys.drop xs.length)
        ((paddedPrefix xs.length ys).reverse ++ zs) (a, valid && decide (xs.length ≤ ys.length)) none := by
  induction xs generalizing ys zs valid scratch with
  | nil =>
      simpa only [result, List.length_nil, List.drop_zero, paddedPrefix, List.reverse_nil,
        List.nil_append, Nat.zero_le, decide_true, Bool.and_true] using!
        pop_working3 base counter src dst hcs hcd [] ys zs (a, valid) scratch
  | cons b bs ih =>
      simp only [List.length_cons, result]
      rw [show readStore counter (working3 base counter src dst (b :: bs) ys zs
        (a, valid) scratch) = working3 base counter src dst bs ys zs (a, valid) (some b) from
          pop_working3 base counter src dst hcs hcd (b :: bs) ys zs (a, valid) scratch]
      rw [body_working base counter src dst hsd, ih]
      simp only [paddedPrefix, List.reverse_cons, List.append_assoc, List.singleton_append,
        Bool.and_assoc, enough_succ]
      congr 1
      cases ys <;> simp

/-- A linear-time prefix extractor with exact rejection information. It
consumes the count, preserves unrelated stacks, and clears scratch control. -/
theorem takeBits_executes (base : K → List Bool) (counter src dst : K)
    (hcs : counter ≠ src) (hcd : counter ≠ dst) (hsd : src ≠ dst)
    (xs ys zs : List Bool) (a : Aux) (valid : Bool) (scratch : Option Bool) :
    ∃ c, c ≤ 4 * xs.length + 2 ∧
      Executes (takeBits counter src dst)
        (working3 base counter src dst xs ys zs (a, valid) scratch)
        (working3 base counter src dst [] (ys.drop xs.length)
          ((paddedPrefix xs.length ys).reverse ++ zs)
          (a, valid && decide (xs.length ≤ ys.length)) none) c := by
  have h := repeat_executes counter (body src dst) (bodyStore src dst) (fun _ => True) 2
    (fun _ _ => trivial) (fun _ _ => trivial)
    (fun s _ => by simp [bodyStore, Op.apply, hcs, hcd])
    (fun s _ => ⟨2, le_refl _, body_executes src dst s⟩)
    (working3 base counter src dst xs ys zs (a, valid) scratch) trivial
  have he : (working3 base counter src dst xs ys zs (a, valid) scratch).stk counter = xs := by
    simp [working3, hcs, hcd]
  rw [he, result_working base counter src dst hcs hcd hsd] at h
  exact h

theorem takeBits_store (counter src dst : K)
    (hcs : counter ≠ src) (hcd : counter ≠ dst) (hsd : src ≠ dst)
    (s : BitStore K (Aux × Bool)) :
    ∃ c, c ≤ 4 * (s.stk counter).length + 2 ∧
      Executes (takeBits counter src dst) s
        ⟨((s.state.1.1, s.state.1.2 && decide ((s.stk counter).length ≤ (s.stk src).length)), none),
          Function.update (Function.update (Function.update s.stk counter [])
            src ((s.stk src).drop (s.stk counter).length)) dst
            ((paddedPrefix (s.stk counter).length (s.stk src)).reverse ++ s.stk dst)⟩ c := by
  simpa only [working3, Function.update_eq_self, Prod.mk.eta] using
    takeBits_executes s.stk counter src dst hcs hcd hsd
      (s.stk counter) (s.stk src) (s.stk dst) s.state.1.1 s.state.1.2 s.state.2

end Lax751879Proofs.StackTake
