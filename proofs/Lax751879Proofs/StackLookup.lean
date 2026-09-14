import Lax751879Proofs.StackRepeat

namespace Lax751879Proofs.StackLookup

open StackProgram StackTransfer StackRepeat

variable {K Aux : Type} [DecidableEq K]

def discard (table : K) : BitProgram K Aux :=
  .atom (.pop table (fun s _ => s))

def discardStore (table : K) (s : BitStore K Aux) : BitStore K Aux :=
  Op.apply (.pop table (fun s _ => s)) s

/-- Consume an index counter, skip that many table bits, and store the next
bit (or exhaustion) in auxiliary control. -/
def lookup (index table : K) : BitProgram K (Aux × Option Bool) :=
  .seq (repeatCount index (discard table))
    (.atom (.pop table (fun s b => ((s.1.1, b), none))))

theorem discard_working (base : K → List Bool) (index table : K)
    (xs ys : List Bool) (a : Aux) (scratch : Option Bool) :
    discardStore table (working base index table xs ys a scratch) =
      working base index table xs ys.tail a scratch := by
  apply Store.ext
  · rfl
  · funext k
    by_cases ht : k = table <;> simp_all [discardStore, Op.apply, working]

theorem result_working (base : K → List Bool) (index table : K) (hne : index ≠ table)
    (xs ys : List Bool) (a : Aux) (scratch : Option Bool) :
    result index (discardStore table) xs.length (working base index table xs ys a scratch) =
      working base index table [] (ys.drop xs.length) a none := by
  induction xs generalizing ys scratch with
  | nil =>
      simpa only [result, List.length_nil, List.drop_zero] using!
        pop_working base index table hne [] ys a scratch
  | cons b bs ih =>
      simp only [List.length_cons, result]
      rw [show readStore index (working base index table (b :: bs) ys a scratch) =
        working base index table bs ys a (some b) from
          pop_working base index table hne (b :: bs) ys a scratch]
      rw [discard_working, ih]
      congr 1
      cases ys <;> simp

theorem skip_executes (base : K → List Bool) (index table : K) (hne : index ≠ table)
    (xs ys : List Bool) (a : Aux) (scratch : Option Bool) :
    ∃ c, c ≤ 3 * xs.length + 2 ∧
      Executes (repeatCount index (discard table)) (working base index table xs ys a scratch)
        (working base index table [] (ys.drop xs.length) a none) c := by
  have h := repeat_executes index (discard table) (discardStore table) (fun _ => True) 1
    (fun _ _ => trivial) (fun _ _ => trivial)
    (fun s _ => by simp [discardStore, Op.apply, hne])
    (fun s _ => ⟨1, le_refl _, Executes.atom _ _⟩)
    (working base index table xs ys a scratch) trivial
  have he : (working base index table xs ys a scratch).stk index = xs := by
    simp [working, hne]
  rw [he, result_working base index table hne] at h
  exact h

/-- An actual linear-time table access, valid even for an out-of-range
index; exhaustion returns none. The counter and consumed table prefix are
discarded, and unrelated stacks and auxiliary control are preserved. -/
theorem lookup_executes (base : K → List Bool) (index table : K) (hne : index ≠ table)
    (xs ys : List Bool) (a : Aux) (old : Option Bool) (scratch : Option Bool) :
    ∃ c, c ≤ 3 * xs.length + 3 ∧
      Executes (lookup index table) (working base index table xs ys (a, old) scratch)
        (working base index table [] (ys.drop (xs.length + 1))
          (a, ys[xs.length]?) none) c := by
  obtain ⟨c, hc, hh⟩ := skip_executes base index table hne xs ys (a, old) scratch
  have hp := Executes.atom
    (.pop table (fun s : (Aux × Option Bool) × Option Bool => fun b => ((s.1.1, b), none)))
    (working base index table [] (ys.drop xs.length) (a, old) none)
  have he : Op.apply
      (.pop table (fun s : (Aux × Option Bool) × Option Bool => fun b => ((s.1.1, b), none)))
      (working base index table [] (ys.drop xs.length) (a, old) none) =
      working base index table [] (ys.drop (xs.length + 1)) (a, ys[xs.length]?) none := by
    apply Store.ext
    · simp [Op.apply, working]
    · funext k
      by_cases ht : k = table <;> simp_all [Op.apply, working, List.tail_drop]
  rw [he] at hp
  exact ⟨c + 1, by omega, Executes.seq hh hp⟩

end Lax751879Proofs.StackLookup
