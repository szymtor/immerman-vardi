import Lax751879Proofs.StackMaterialize

namespace Lax751879Proofs.StackTableRound

open StackProgram StackTransfer StackBoolean StackTuples StackMaterialize

variable {K Aux : Type} [DecidableEq K]

/-- Read the previous table throughout construction of the complete next
table. Only then discard the old table and install the new one. -/
def round (domain tmp rev current next : K) (slots : List (K × K))
    (body : EvalProgram K Aux) : EvalProgram K Aux :=
  .seq (materialize domain tmp rev next slots body)
    (.seq (StackClear.clear current)
      (.seq (transfer next rev) (transfer rev current)))

/-- Two transfers retain canonical order when replacing the old table. The
round restores every stack except current, including the next-table buffer. -/
theorem round_executes (s : EvalStore K Aux) (domain tmp rev current next : K)
    (slots : List (K × K))
    (hsep : (domain :: tmp :: rev :: current :: next :: ports slots).Nodup)
    (hempty : ∀ key, key ∈ tmp :: rev :: next :: ports slots → s.stk key = [])
    (body : EvalProgram K Aux) (b : List Nat → Bool) (n B : Nat)
    (hdomain : s.stk domain = List.replicate n true)
    (hbody : ∀ values, values.length = slots.length → (∀ i ∈ values, i < n) →
      ∀ remaining, remaining.length = slots.length → ∀ bits scratch,
      ∃ c, c ≤ B ∧ Returns body
        (packTuple (payload s rev) slots bits values remaining scratch) (b values) c) :
    ∃ c, c ≤ StackTuples.cost n (B + 2) slots.length +
        9 * n ^ slots.length + 2 * (s.stk current).length + 9 ∧
      Executes (round domain tmp rev current next slots body) s
        (setStack (result false s) current (table n slots.length b)) c := by
  have hnext : s.stk next = [] := hempty next (by simp)
  have hrev : s.stk rev = [] := hempty rev (by simp)
  have hcn : current ≠ next := by
    simp only [List.nodup_cons, List.mem_cons, not_or] at hsep
    tauto
  have hrc : rev ≠ current := by
    simp only [List.nodup_cons, List.mem_cons, not_or] at hsep
    tauto
  have hrn : rev ≠ next := by
    simp only [List.nodup_cons, List.mem_cons, not_or] at hsep
    tauto
  have hmat : (domain :: tmp :: rev :: next :: ports slots).Nodup := by
    simp only [List.nodup_cons, List.mem_cons, not_or] at hsep ⊢
    tauto
  obtain ⟨c, hc, hm⟩ := materialize_executes s domain tmp rev next slots hmat
    (by intro key hk; apply hempty key; simp only [List.mem_cons] at hk ⊢; tauto)
    body b n B hdomain hbody
  rw [hnext, List.append_nil] at hm
  let bits := table n slots.length b
  let u := setStack (result false s) next bits
  have hclear := StackClear.clear_store current u
  have hu : u.stk current = s.stk current := by simp [u, setStack, result, hcn]
  rw [hu] at hclear
  let v : EvalStore K Aux := ⟨(u.state.1, none), Function.update u.stk current []⟩
  have hfirst := transfer_store next rev (Ne.symm hrn) v
  have hvn : v.stk next = bits := by simp [v, u, setStack, Ne.symm hcn]
  have hvr : v.stk rev = [] := by simp [v, u, setStack, result, hrc, hrn, hrev]
  rw [hvn, hvr, List.append_nil] at hfirst
  let w : EvalStore K Aux :=
    ⟨(v.state.1, none), Function.update (Function.update v.stk next []) rev bits.reverse⟩
  have hsecond := transfer_store rev current hrc w
  have hwr : w.stk rev = bits.reverse := by simp [w]
  have hwc : w.stk current = [] := by simp [w, v, Ne.symm hrc, hcn]
  rw [hwr, hwc, List.reverse_reverse, List.append_nil, List.length_reverse] at hsecond
  have he : (⟨(w.state.1, none), Function.update (Function.update w.stk rev []) current bits⟩ :
      EvalStore K Aux) = setStack (result false s) current bits := by
    apply Store.ext
    · rfl
    · funext key
      by_cases hkey : key = current
      · subst key; simp [setStack]
      · by_cases hkey' : key = next
        · subst key; simp [w, v, u, setStack, result, hkey, Ne.symm hrn, hnext]
        · by_cases hkey'' : key = rev
          · subst key; simp [w, v, u, setStack, result, hkey, hrev]
          · simp [w, v, u, setStack, result, hkey, hkey', hkey'']
  rw [he] at hsecond
  have hlen : bits.length = n ^ slots.length := table_length n slots.length b
  rw [hlen] at hfirst hsecond
  exact ⟨c + ((2 * (s.stk current).length + 2) +
      ((3 * n ^ slots.length + 2) + (3 * n ^ slots.length + 2))), by omega,
    Executes.seq hm (Executes.seq hclear (Executes.seq hfirst hsecond))⟩

end Lax751879Proofs.StackTableRound
