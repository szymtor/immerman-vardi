import Lax979537Proofs.StackTake
import Lax979537Proofs.StackPower

namespace Lax979537Proofs.StackReadTable

open StackProgram StackTransfer

variable {K Aux : Type} [DecidableEq K]

/-- Read one dense relation table, using the unary domain size and a fixed
nesting depth. On insufficient input the validity bit becomes false. -/
def readTable (domain input table count tmp rev : K) (counters : List K) :
    BitProgram K (Aux × Bool) :=
  .seq (StackPower.power domain count tmp counters)
    (.seq (StackTake.takeBits count input rev) (transfer rev table))

def result (input table : K) (n k : Nat) (s : BitStore K (Aux × Bool)) : BitStore K (Aux × Bool) :=
  ⟨((s.state.1.1, s.state.1.2 && decide (n ^ k ≤ (s.stk input).length)), none),
    Function.update (Function.update s.stk input ((s.stk input).drop (n ^ k)))
      table (StackTake.paddedPrefix (n ^ k) (s.stk input))⟩

noncomputable def costPolynomial (k : Nat) : Polynomial Nat :=
  StackPower.costPolynomial k + Polynomial.C 7 * Polynomial.X ^ k + Polynomial.C 4

def cost (k n : Nat) : Nat := StackPower.cost k n + 7 * n ^ k + 4

theorem eval_costPolynomial (k n : Nat) : (costPolynomial k).eval n = cost k n := by
  simp [costPolynomial, cost, StackPower.eval_costPolynomial]

theorem readTable_executes (domain input table count tmp rev : K)
    (hdc : domain ≠ count) (hdt : domain ≠ tmp) (hct : count ≠ tmp)
    (hci : count ≠ input) (hcr : count ≠ rev)
    (hir : input ≠ rev) (hib : input ≠ table) (hrb : rev ≠ table)
    (counters : List K) (hnodup : counters.Nodup)
    (hslots : ∀ c ∈ counters, c ≠ domain ∧ c ≠ count ∧ c ≠ tmp)
    (n : Nat) (s : BitStore K (Aux × Bool))
    (hd : s.stk domain = List.replicate n true) (ht : s.stk tmp = [])
    (hc : s.stk count = []) (hr : s.stk rev = []) (hb : s.stk table = [])
    (hs : ∀ c ∈ counters, s.stk c = []) :
    ∃ t, t ≤ (costPolynomial counters.length).eval n ∧
      Executes (readTable domain input table count tmp rev counters) s
        (result input table n counters.length s) t := by
  let m := n ^ counters.length
  let bits := StackTake.paddedPrefix m (s.stk input)
  let valid := s.state.1.2 && decide (m ≤ (s.stk input).length)
  let u := StackPower.addTokens count m s
  let v : BitStore K (Aux × Bool) :=
    ⟨((s.state.1.1, valid), none),
      Function.update (Function.update s.stk input ((s.stk input).drop m)) rev bits.reverse⟩
  obtain ⟨a, ha, hp⟩ := StackPower.power_executes domain count tmp hdc hdt hct
    counters hnodup hslots n s hd ht hs
  change Executes _ s u a at hp
  have htake : ∃ b, b ≤ 4 * m + 2 ∧ Executes (StackTake.takeBits count input rev) u v b := by
    have h := StackTake.takeBits_store count input rev hci hcr hir u
    have huc : u.stk count = List.replicate m true := by simp [u, StackPower.addTokens, hc]
    have hui : u.stk input = s.stk input := by simp [u, StackPower.addTokens, Ne.symm hci]
    have hur : u.stk rev = [] := by simp [u, StackPower.addTokens, Ne.symm hcr, hr]
    rw [huc, hui, hur] at h
    simp only [List.length_replicate, List.append_nil] at h
    have he : (⟨((u.state.1.1, u.state.1.2 && decide (m ≤ (s.stk input).length)), none),
        Function.update (Function.update (Function.update u.stk count [])
          input ((s.stk input).drop m)) rev bits.reverse⟩ : BitStore K (Aux × Bool)) = v := by
      apply Store.ext
      · rfl
      · simp [u, StackPower.addTokens, v, Function.update_idem, ← hc]
    rw [he] at h
    exact h
  obtain ⟨b, hbtime, htake⟩ := htake
  have hmove := transfer_store rev table hrb v
  have hvr : v.stk rev = bits.reverse := by simp [v]
  have hvb : v.stk table = [] := by simp [v, Ne.symm hrb, Ne.symm hib, hb]
  rw [hvr, hvb, List.reverse_reverse, List.append_nil, List.length_reverse] at hmove
  have he : (⟨(v.state.1, none), Function.update (Function.update v.stk rev []) table bits⟩ :
      BitStore K (Aux × Bool)) = result input table n counters.length s := by
    apply Store.ext
    · rfl
    · funext k
      by_cases hkb : k = table
      · subst k; simp [result, bits, m]
      · by_cases hkr : k = rev
        · subst k; simp [v, result, hkb, Ne.symm hir, hr]
        · simp [v, result, hkb, hkr, bits, m, Function.update_apply]
  rw [he] at hmove
  have hlen : bits.length = m := StackTake.prefix_length m _
  rw [hlen] at hmove
  refine ⟨a + (b + (3 * m + 2)), ?_, Executes.seq hp (Executes.seq htake hmove)⟩
  simp only [costPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X]
  change a + (b + (3 * m + 2)) ≤ (StackPower.costPolynomial counters.length).eval n + 7 * m + 4
  omega

theorem result_preserves (input table key : K) (hi : key ≠ input) (ht : key ≠ table)
    (n k : Nat) (s : BitStore K (Aux × Bool)) :
    (result input table n k s).stk key = s.stk key := by
  simp [result, hi, ht]

theorem result_table (input table : K) (n k : Nat) (s : BitStore K (Aux × Bool))
    (h : n ^ k ≤ (s.stk input).length) :
    (result input table n k s).stk table = (s.stk input).take (n ^ k) := by
  simp [result, StackTake.prefix_eq_take _ _ h]

end Lax979537Proofs.StackReadTable
