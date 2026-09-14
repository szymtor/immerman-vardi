import Lax751879Proofs.StackTransfer
import Lax751879Proofs.Decoding

namespace Lax751879Proofs.StackUnary

open StackProgram StackTransfer

variable {K Aux : Type}

/-- Count the leading true bits, distinguishing a delimiter from exhaustion. -/
def splitUnary : List Bool → Nat × Option (List Bool)
  | [] => (0, none)
  | false :: xs => (0, some xs)
  | true :: xs => let r := splitUnary xs; (r.1 + 1, r.2)

def finished (rest : Option (List Bool)) : Option Bool := rest.map (fun _ => false)

theorem splitUnary_le (xs : List Bool) : (splitUnary xs).1 ≤ xs.length := by
  induction xs with
  | nil => simp [splitUnary]
  | cons b xs ih => cases b <;> simp [splitUnary]; omega

theorem splitUnary_correct (xs : List Bool) :
    Decoding.readUnary xs = (splitUnary xs).2.map (fun rest => ((splitUnary xs).1, rest)) := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      cases b with
      | false => rfl
      | true =>
          simp only [Decoding.readUnary, splitUnary, ih]
          cases (splitUnary xs).2 <;> rfl

theorem splitUnary_rest_le (xs : List Bool) :
    ((splitUnary xs).2.getD []).length ≤ xs.length := by
  induction xs with
  | nil => simp [splitUnary]
  | cons b xs ih => cases b <;> simp only [splitUnary, List.length_cons, Option.getD_some] <;> omega

def body (src counter : K) : BitProgram K Aux :=
  .seq (.atom (.push counter (fun _ => true))) (read src)

def loop (src counter : K) : BitProgram K Aux :=
  .loop (fun s => s.2 == some true) (body src counter)

/-- Parse a unary number, storing its value as a unary counter stack. The
scratch bit is `some false` on success and `none` on a missing delimiter. -/
def parse (src counter : K) : BitProgram K Aux :=
  .seq (read src) (loop src counter)

theorem loop_executes [DecidableEq K] (base : K → List Bool) (src counter : K)
    (hne : src ≠ counter) (xs ys : List Bool) (a : Aux) :
    Executes (loop src counter)
      (working base src counter xs.tail ys a xs.head?)
      (working base src counter ((splitUnary xs).2.getD [])
        (List.replicate (splitUnary xs).1 true ++ ys) a (finished (splitUnary xs).2))
      (3 * (splitUnary xs).1 + 1) := by
  induction xs generalizing ys with
  | nil => exact Executes.loop_false rfl
  | cons b xs ih =>
      cases b with
      | false => exact Executes.loop_false rfl
      | true =>
          have hp := Executes.atom (.push counter (fun _ : Aux × Option Bool => true))
            (working base src counter xs ys a (some true))
          have hpush : Op.apply (.push counter (fun _ : Aux × Option Bool => true))
              (working base src counter xs ys a (some true)) =
              working base src counter xs (true :: ys) a (some true) := by
            apply Store.ext
            · rfl
            · funext k
              by_cases hk : k = counter <;> simp_all [Op.apply, working]
          rw [hpush] at hp
          have hr := Executes.atom
            (.pop src (fun s : Aux × Option Bool => fun b => (s.1, b)))
            (working base src counter xs (true :: ys) a (some true))
          rw [pop_working base src counter hne] at hr
          have hh := Executes.loop_true (p := body src counter)
            (b := fun s : Aux × Option Bool => s.2 == some true) rfl
            (Executes.seq hp hr) (ih (true :: ys))
          have ht : (1 + 1) + (3 * (splitUnary xs).1 + 1) + 1 =
              3 * ((splitUnary xs).1 + 1) + 1 := by omega
          simpa only [splitUnary, List.tail_cons, List.head?_cons, List.replicate_succ',
            List.append_assoc, List.singleton_append, ht] using hh

theorem parse_executes [DecidableEq K] (base : K → List Bool) (src counter : K)
    (hne : src ≠ counter) (xs ys : List Bool) (a : Aux) (scratch : Option Bool) :
    Executes (parse src counter) (working base src counter xs ys a scratch)
      (working base src counter ((splitUnary xs).2.getD [])
        (List.replicate (splitUnary xs).1 true ++ ys) a (finished (splitUnary xs).2))
      (3 * (splitUnary xs).1 + 2) := by
  have hr := Executes.atom (.pop src (fun s : Aux × Option Bool => fun b => (s.1, b)))
    (working base src counter xs ys a scratch)
  rw [pop_working base src counter hne] at hr
  have h := Executes.seq hr (loop_executes base src counter hne xs ys a)
  have ht : 1 + (3 * (splitUnary xs).1 + 1) = 3 * (splitUnary xs).1 + 2 := by omega
  simpa only [ht] using h

theorem parse_linear_bound (xs : List Bool) :
    3 * (splitUnary xs).1 + 2 ≤ 3 * xs.length + 2 := by
  have := splitUnary_le xs
  omega

end Lax751879Proofs.StackUnary
