import Lax751879Proofs.StackRepeat

namespace Lax751879Proofs.StackPower

open StackProgram StackTransfer StackRepeat

variable {K Aux : Type} [DecidableEq K]

def addTokens (out : K) (m : Nat) (s : BitStore K Aux) : BitStore K Aux :=
  ⟨(s.state.1, none), Function.update s.stk out (List.replicate m true ++ s.stk out)⟩

/-- One copied domain counter per nesting level. Even the zero-th power
works on the empty domain: it contributes one token. -/
def power (domain out tmp : K) : List K → BitProgram K Aux
  | [] => .seq (.atom (.push out (fun _ => true)))
      (.atom (.load (fun s => (s.1, none))))
  | counter :: rest => .seq (StackCopy.copy domain counter tmp)
      (repeatCount counter (power domain out tmp rest))

def cost : Nat → Nat → Nat
  | 0, _ => 2
  | k + 1, n => 7 * n + 6 + n * (cost k n + 2)

noncomputable def costPolynomial : Nat → Polynomial Nat
  | 0 => Polynomial.C 2
  | k + 1 => Polynomial.C 7 * Polynomial.X + Polynomial.C 6 +
      Polynomial.X * (costPolynomial k + Polynomial.C 2)

theorem eval_costPolynomial (k n : Nat) : (costPolynomial k).eval n = cost k n := by
  induction k with
  | zero => simp [costPolynomial, cost]
  | succ k ih => simp [costPolynomial, cost, ih]

theorem addTokens_working (base : K → List Bool) (counter out : K)
    (xs ys : List Bool) (a : Aux) (scratch : Option Bool) (m : Nat) :
    addTokens out m (working base counter out xs ys a scratch) =
      working base counter out xs (List.replicate m true ++ ys) a none := by
  apply Store.ext
  · rfl
  · funext k
    by_cases hk : k = out <;> simp_all [addTokens, working]

theorem result_addTokens (base : K → List Bool) (counter out : K) (hne : counter ≠ out)
    (xs ys : List Bool) (a : Aux) (scratch : Option Bool) (m : Nat) :
    result counter (addTokens out m) xs.length (working base counter out xs ys a scratch) =
      working base counter out [] (List.replicate (m * xs.length) true ++ ys) a none := by
  induction xs generalizing ys scratch with
  | nil =>
      simpa only [result, List.length_nil, Nat.mul_zero, List.replicate_zero,
        List.nil_append] using! pop_working base counter out hne [] ys a scratch
  | cons b bs ih =>
      simp only [List.length_cons, result]
      rw [show readStore counter (working base counter out (b :: bs) ys a scratch) =
        working base counter out bs ys a (some b) from
          pop_working base counter out hne (b :: bs) ys a scratch]
      rw [addTokens_working, ih]
      rw [Nat.mul_succ, List.replicate_add, List.append_assoc]

/-- Generate n^k unary tokens, preserving the domain counter, auxiliary
control, and all unrelated stacks. All private counters are returned empty.
The polynomial depends only on the fixed nesting depth k. -/
theorem power_executes (domain out tmp : K)
    (hdo : domain ≠ out) (hdt : domain ≠ tmp) (hot : out ≠ tmp)
    (counters : List K) (hnodup : counters.Nodup)
    (hslots : ∀ c ∈ counters, c ≠ domain ∧ c ≠ out ∧ c ≠ tmp)
    (n : Nat) (s : BitStore K Aux) (hd : s.stk domain = List.replicate n true)
    (ht : s.stk tmp = []) (hc : ∀ c ∈ counters, s.stk c = []) :
    ∃ t, t ≤ (costPolynomial counters.length).eval n ∧
      Executes (power domain out tmp counters) s (addTokens out (n ^ counters.length) s) t := by
  induction counters generalizing s with
  | nil =>
      refine ⟨2, by simp [costPolynomial], ?_⟩
      have hp := Executes.atom (.push out (fun _ : Aux × Option Bool => true)) s
      have hl := Executes.atom (.load (fun q : Aux × Option Bool => (q.1, none)))
        (Op.apply (.push out (fun _ : Aux × Option Bool => true)) s)
      simpa [power, addTokens, Op.apply] using Executes.seq hp hl
  | cons counter rest ih =>
      obtain ⟨hnot, hrest⟩ := List.nodup_cons.mp hnodup
      obtain ⟨hcd, hco, hct⟩ := hslots counter (by simp)
      have hslots' : ∀ c ∈ rest, c ≠ domain ∧ c ≠ out ∧ c ≠ tmp :=
        fun c hm => hslots c (by simp [hm])
      have hcounter := hc counter (by simp)
      let u : BitStore K Aux :=
        ⟨(s.state.1, none), Function.update s.stk counter (List.replicate n true)⟩
      have hcopy := StackCopy.copy_store domain counter tmp (Ne.symm hcd) hdt hct s ht
      rw [hd, hcounter, List.append_nil, List.length_replicate] at hcopy
      change Executes _ s u _ at hcopy
      let Valid : BitStore K Aux → Prop := fun q =>
        q.stk domain = List.replicate n true ∧ q.stk tmp = [] ∧
          ∀ c ∈ rest, q.stk c = []
      have hread : ∀ q, Valid q → Valid (readStore counter q) := by
        intro q hq
        refine ⟨?_, ?_, ?_⟩
        · simpa [readStore, Op.apply, Ne.symm hcd] using hq.1
        · simpa [readStore, Op.apply, Ne.symm hct] using hq.2.1
        · intro c hm
          have hne : c ≠ counter := fun he => hnot (he ▸ hm)
          simpa [readStore, Op.apply, hne] using hq.2.2 c hm
      have hf : ∀ q, Valid q → Valid (addTokens out (n ^ rest.length) q) := by
        intro q hq
        refine ⟨?_, ?_, ?_⟩
        · simpa [addTokens, hdo] using hq.1
        · simpa [addTokens, Ne.symm hot] using hq.2.1
        · intro c hm
          simpa [addTokens, (hslots' c hm).2.1] using hq.2.2 c hm
      have hframe : ∀ q, Valid q → (addTokens out (n ^ rest.length) q).stk counter =
          q.stk counter := fun q _ => by simp [addTokens, hco]
      have hbody : ∀ q, Valid q → ∃ t, t ≤ (costPolynomial rest.length).eval n ∧
          Executes (power domain out tmp rest) q (addTokens out (n ^ rest.length) q) t := by
        intro q hq
        exact ih hrest hslots' q hq.1 hq.2.1 hq.2.2
      have hu : Valid u := by
        refine ⟨?_, ?_, ?_⟩
        · simpa [u, Ne.symm hcd] using hd
        · simpa [u, Ne.symm hct] using ht
        · intro c hm
          have hne : c ≠ counter := fun he => hnot (he ▸ hm)
          simpa [u, hne] using hc c (by simp [hm])
      obtain ⟨t, htime, hexec⟩ := repeat_executes counter (power domain out tmp rest)
        (addTokens out (n ^ rest.length)) Valid ((costPolynomial rest.length).eval n)
        hread hf hframe hbody u hu
      have hlen : (u.stk counter).length = n := by simp [u]
      rw [hlen] at htime hexec
      have hu' : u = working s.stk counter out (List.replicate n true) (s.stk out)
          s.state.1 none := by
        apply Store.ext
        · rfl
        · funext k
          by_cases ho : k = out
          · subst k; simp [u, working, Ne.symm hco]
          · simp [u, working, ho]
      have hresult : result counter (addTokens out (n ^ rest.length)) n u =
          addTokens out (n ^ (counter :: rest).length) s := by
        have h := result_addTokens s.stk counter out hco (List.replicate n true)
          (s.stk out) s.state.1 none (n ^ rest.length)
        simp only [List.length_replicate] at h
        rw [hu', h]
        simp [working, addTokens, pow_succ, ← hcounter]
      rw [hresult] at hexec
      refine ⟨(7 * n + 4) + t, ?_, Executes.seq hcopy hexec⟩
      simp only [List.length_cons, costPolynomial, Polynomial.eval_add,
        Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      rw [Nat.mul_comm n]
      omega

end Lax751879Proofs.StackPower
