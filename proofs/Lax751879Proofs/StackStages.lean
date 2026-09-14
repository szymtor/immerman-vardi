import Lax751879Proofs.StackPower
import Lax751879Proofs.StackFor

namespace Lax751879Proofs.StackStages

open StackProgram StackTransfer StackFor

variable {K Aux α : Type} [DecidableEq K]

def prepared (base : α → BitStore K Aux) (bound : K) (m : Nat) (a : α) : BitStore K Aux :=
  ⟨((base a).state.1, none), Function.update (base a).stk bound (List.replicate m true)⟩

/-- Prepare the polynomial stage bound on a stack, run a fixed body under
that bound, and remove the bound. Neither n nor its power occurs in the code. -/
def stages (domain bound counter coord tmp : K) (powerCounters : List K)
    (body : BitProgram K Aux) : BitProgram K Aux :=
  .seq (StackPower.power domain bound tmp powerCounters)
    (.seq (forValues bound counter coord tmp body) (StackClear.clear bound))

noncomputable def costPolynomial (B : Polynomial Nat) (k : Nat) : Polynomial Nat :=
  StackPower.costPolynomial k + (B + 14) * Polynomial.X ^ k + 10

theorem eval_costPolynomial (B : Polynomial Nat) (n k : Nat) :
    (costPolynomial B k).eval n = StackPower.cost k n + (B.eval n + 14) * n ^ k + 10 := by
  simp [costPolynomial, StackPower.eval_costPolynomial]

theorem foldRange_iterate (f : α → α) (start count : Nat) (a : α) :
    foldRange (fun _ => f) start count a = (f^[count]) a := by
  induction count generalizing start a with
  | zero => rfl
  | succ count ih => simp [foldRange, ih, Function.iterate_succ_apply]

/-- Given the actual bounded executions of one stage, obtain n^k concrete
stage executions and the corresponding mathematical iterate. All stage and
power counters are returned empty; arbitrary surrounding data is framed by
the semantic store family. -/
theorem stages_executes (base : α → BitStore K Aux) (domain bound counter coord tmp : K)
    (hsep : [domain, bound, counter, coord, tmp].Nodup)
    (powerCounters : List K) (hpool : powerCounters.Nodup)
    (hpoolFresh : ∀ key ∈ powerCounters, key ∉ [domain, bound, counter, coord, tmp])
    (hempty : ∀ a key, key ∈ [bound, counter, coord, tmp] ++ powerCounters → (base a).stk key = [])
    (body : BitProgram K Aux) (f : α → α) (n B : Nat)
    (hbody : ∀ i, i < n ^ powerCounters.length → ∀ a remaining scratch,
      ∃ c scratch', c ≤ B ∧ Executes body
        (pack (prepared base bound (n ^ powerCounters.length)) counter coord a i remaining scratch)
        (pack (prepared base bound (n ^ powerCounters.length)) counter coord (f a) i remaining scratch') c)
    (a : α) (hdomain : (base a).stk domain = List.replicate n true) :
    ∃ c, c ≤ StackPower.cost powerCounters.length n +
        (B + 14) * n ^ powerCounters.length + 10 ∧
      Executes (stages domain bound counter coord tmp powerCounters body) (base a)
        (reset (base ((f^[n ^ powerCounters.length]) a))) c := by
  have hb (a : α) : (base a).stk bound = [] := hempty a bound (by simp)
  have hc (a : α) : (base a).stk counter = [] := hempty a counter (by simp)
  have hx (a : α) : (base a).stk coord = [] := hempty a coord (by simp)
  have ht (a : α) : (base a).stk tmp = [] := hempty a tmp (by simp)
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true,
    not_or, and_true] at hsep
  have hdb : domain ≠ bound := by tauto
  have hdt : domain ≠ tmp := by tauto
  have hbt : bound ≠ tmp := by tauto
  have hcb : counter ≠ bound := by tauto
  have hxb : coord ≠ bound := by tauto
  have hloop : [bound, counter, coord, tmp].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true,
      not_or, and_true]
    tauto
  obtain ⟨p, hp, hpower⟩ := StackPower.power_executes domain bound tmp hdb hdt hbt
    powerCounters hpool (by
      intro key hk
      have hf := hpoolFresh key hk
      simp only [List.mem_cons, List.not_mem_nil, not_false_eq_true, not_or, and_true] at hf
      tauto) n (base a) hdomain (ht a)
    (fun key hk => hempty a key (by simp [hk]))
  rw [StackPower.eval_costPolynomial] at hp
  have he : StackPower.addTokens bound (n ^ powerCounters.length) (base a) =
      prepared base bound (n ^ powerCounters.length) a := by
    simp [StackPower.addTokens, prepared, hb]
  rw [he] at hpower
  obtain ⟨c, hcost, hfor⟩ := forValues_executes (prepared base bound (n ^ powerCounters.length))
    bound counter coord tmp hloop body (fun _ => f) (n ^ powerCounters.length) B
    (by intro a; simp [prepared, hcb, hc])
    (by intro a; simp [prepared, hxb, hx])
    (by intro a; simp [prepared, Ne.symm hbt, ht]) hbody a (by simp [prepared])
  rw [foldRange_iterate] at hfor
  let final := (f^[n ^ powerCounters.length]) a
  have hclear := StackClear.clear_store bound
    (reset (prepared base bound (n ^ powerCounters.length) final))
  have hlen : (reset (prepared base bound (n ^ powerCounters.length) final)).stk bound =
      List.replicate (n ^ powerCounters.length) true := by simp [reset, prepared]
  rw [hlen, List.length_replicate] at hclear
  have he' : (⟨((reset (prepared base bound (n ^ powerCounters.length) final)).state.1, none),
      Function.update (reset (prepared base bound (n ^ powerCounters.length) final)).stk bound []⟩ :
      BitStore K Aux) = reset (base final) := by
    simp [reset, prepared, Function.update_idem, ← hb final]
  rw [he'] at hclear
  refine ⟨p + (c + (2 * n ^ powerCounters.length + 2)), ?_,
    Executes.seq hpower (Executes.seq hfor hclear)⟩
  simp only [Nat.add_mul] at hcost ⊢
  omega

end Lax751879Proofs.StackStages
