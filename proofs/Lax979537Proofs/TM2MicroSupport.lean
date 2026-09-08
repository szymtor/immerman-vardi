import Lax979537Proofs.TM2Micro

namespace Lax979537Proofs.TM2MicroSupport

open Turing TM2Micro

open scoped Classical in
noncomputable def controls (tm : FinTM2) : Finset (Cursor tm.Γ tm.Λ tm.σ) :=
  letI := tm.ΛFin
  Finset.univ.image Cursor.boundary ∪
    Finset.univ.biUnion (fun l : tm.Λ => (TM2.stmts₁ (tm.m l)).image Cursor.instruction)

theorem boundary_mem (tm : FinTM2) (l : Option tm.Λ) : Cursor.boundary l ∈ controls tm := by
  classical
  simp [controls]

theorem instruction_mem (tm : FinTM2) (q : TM2.Stmt tm.Γ tm.Λ tm.σ) :
    Cursor.instruction q ∈ controls tm ↔ ∃ l, q ∈ TM2.stmts₁ (tm.m l) := by
  classical
  simp [controls]

theorem instruction_sub (tm : FinTM2) {p q : TM2.Stmt tm.Γ tm.Λ tm.σ}
    (hq : Cursor.instruction q ∈ controls tm) (hp : p ∈ TM2.stmts₁ q) :
    Cursor.instruction p ∈ controls tm := by
  obtain ⟨l, hl⟩ := (instruction_mem tm q).mp hq
  exact (instruction_mem tm p).mpr ⟨l, TM2.stmts₁_trans hl hp⟩

theorem next_control (tm : FinTM2) (c : Cfg tm.Γ tm.Λ tm.σ) (hc : c.cursor ∈ controls tm) :
    (next tm.m c).cursor ∈ controls tm := by
  classical
  cases c with
  | mk cursor v stk =>
      cases cursor with
      | boundary l =>
          cases l with
          | none => exact hc
          | some l => exact (instruction_mem tm _).mpr ⟨l, TM2.stmts₁_self⟩
      | instruction q =>
          cases q with
          | push k f q | pop k f q | peek k f q | load f q =>
              apply instruction_sub tm hc
              simp [TM2.stmts₁, TM2.stmts₁_self]
          | branch f p q =>
              cases hf : f v <;> simp only [next, hf, Bool.false_eq_true, ↓reduceIte]
              · apply instruction_sub tm hc
                simp [TM2.stmts₁, TM2.stmts₁_self]
              · apply instruction_sub tm hc
                simp [TM2.stmts₁, TM2.stmts₁_self]
          | goto f | halt => exact boundary_mem tm _

theorem next_alphabet (tm : FinTM2) (c : Cfg tm.Γ tm.Λ tm.σ)
    (hc : c.cursor ∈ controls tm) (hs : TM2Alphabet.Valid (TM2Alphabet.alphabet tm : Set (Sigma tm.Γ)) c.stk) :
    TM2Alphabet.Valid (TM2Alphabet.alphabet tm : Set (Sigma tm.Γ)) (next tm.m c).stk := by
  cases c with
  | mk cursor v stk =>
      cases cursor with
      | boundary l => cases l <;> exact hs
      | instruction q =>
          obtain ⟨l, hl⟩ := (instruction_mem tm q).mp hc
          have hq := TM2Alphabet.supports_substatement hl (TM2Alphabet.machine_supports tm l)
          cases q with
          | push k f q =>
              intro j a ha
              by_cases hj : j = k
              · subst j
                simp only [next, instruction, Function.update_self, List.mem_cons] at ha
                rcases ha with rfl | ha
                · exact hq.1 v
                · exact hs k a ha
              · simp only [next, instruction, Function.update_of_ne hj] at ha
                exact hs j a ha
          | pop k f q =>
              intro j a ha
              by_cases hj : j = k
              · subst j
                simp only [next, instruction, Function.update_self] at ha
                exact hs k a (List.mem_of_mem_tail ha)
              · simp only [next, instruction, Function.update_of_ne hj] at ha
                exact hs j a ha
          | branch f p q => cases hf : f v <;> exact hs
          | peek k f q | load f q | goto f | halt => exact hs

theorem iterate_support (tm : FinTM2) (n : Nat) (c : Cfg tm.Γ tm.Λ tm.σ)
    (hc : c.cursor ∈ controls tm) (hs : TM2Alphabet.Valid (TM2Alphabet.alphabet tm : Set (Sigma tm.Γ)) c.stk) :
    ((next tm.m)^[n] c).cursor ∈ controls tm ∧
      TM2Alphabet.Valid (TM2Alphabet.alphabet tm : Set (Sigma tm.Γ)) ((next tm.m)^[n] c).stk := by
  induction n with
  | zero => exact ⟨hc, hs⟩
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact ⟨next_control tm _ ih.1, next_alphabet tm _ ih.1 ih.2⟩

theorem initial_run_support (tm : FinTM2) (xs : List (tm.Γ tm.k₀)) (n : Nat) :
    ((next tm.m)^[n] (boundary (initList tm xs))).cursor ∈ controls tm ∧
      TM2Alphabet.Valid (TM2Alphabet.alphabet tm : Set (Sigma tm.Γ))
        ((next tm.m)^[n] (boundary (initList tm xs))).stk :=
  iterate_support tm n _ (boundary_mem tm _) (TM2Alphabet.initial_valid tm xs)

abbrev Control (tm : FinTM2) := ↥(controls tm)
noncomputable instance (tm : FinTM2) : Fintype (Control tm) := inferInstanceAs (Fintype ↥(controls tm))

theorem length_next (tm : FinTM2) (c : Cfg tm.Γ tm.Λ tm.σ) (key : tm.K) :
    ((next tm.m c).stk key).length ≤ (c.stk key).length + 1 := by
  cases c with
  | mk cursor v stk =>
      cases cursor with
      | boundary l => cases l <;> simp [next, instruction]
      | instruction q =>
          cases q with
          | push k f q =>
              by_cases hk : key = k
              · subst key; simp [next, instruction]
              · simp [next, instruction, hk]
          | pop k f q =>
              by_cases hk : key = k
              · subst key; simp [next, instruction]; omega
              · simp [next, instruction, hk]
          | branch f p q => simp [next, instruction]
          | peek k f q | load f q | goto f | halt => simp [next, instruction]

theorem length_iterate (tm : FinTM2) (n : Nat) (c : Cfg tm.Γ tm.Λ tm.σ) (key : tm.K) :
    (((next tm.m)^[n] c).stk key).length ≤ (c.stk key).length + n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      have h := length_next tm ((next tm.m)^[n] c) key
      omega

theorem initial_length (tm : FinTM2) (xs : List (tm.Γ tm.k₀)) (n : Nat) (key : tm.K) :
    (((next tm.m)^[n] (boundary (initList tm xs))).stk key).length ≤ xs.length + n := by
  have h := length_iterate tm n (boundary (initList tm xs)) key
  have hi : ((initList tm xs).stk key).length ≤ xs.length := by
    by_cases hk : key = tm.k₀
    · subst key; simp [initList]
    · simp [initList, hk]
  exact h.trans (Nat.add_le_add_right hi n)

end Lax979537Proofs.TM2MicroSupport
