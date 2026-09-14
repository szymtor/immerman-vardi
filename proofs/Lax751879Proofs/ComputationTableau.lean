import Lax751879Proofs.LeastFixedPoints
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi

/-!
The local computation-tableau construction used in Immerman's Theorem 2.
The operator contains only positive occurrences of the previous tableau.
Time is bounded but the proof makes no assumption about the number of cells
or symbols. A later syntax translation must represent these coordinates by
tuples in the input structure and instantiate the local rule by a machine.
-/

namespace Lax751879Proofs.ComputationTableau

open Lax751879.LeastFixedPoints

variable {P S : Type} {d : Nat}

structure LocalSystem (P S : Type) (d : Nat) where
  initial : P → S
  neighbor : P → Fin d → P
  transition : P → (Fin d → S) → S

def run (M : LocalSystem P S d) : Nat → P → S
  | 0 => M.initial
  | t + 1 => fun p => M.transition p (fun j => run M t (M.neighbor p j))

abbrev Cell (T : Nat) (P S : Type) := Fin T × P × S

def operator (M : LocalSystem P S d) (T : Nat)
    (R : Set (Cell T P S)) : Set (Cell T P S) :=
  {c | (c.1.val = 0 ∧ c.2.2 = M.initial c.2.1) ∨
    ∃ t : Fin T, c.1.val = t.val + 1 ∧
      ∃ a : Fin d → S,
        (∀ j, (t, M.neighbor c.2.1 j, a j) ∈ R) ∧
        c.2.2 = M.transition c.2.1 a}

theorem operator_monotone (M : LocalSystem P S d) (T : Nat) :
    Monotone (operator M T) := by
  intro R R' h c hc
  rcases hc with hinit | ⟨t, ht, a, ha, he⟩
  · exact Or.inl hinit
  · exact Or.inr ⟨t, ht, a, fun j => h (ha j), he⟩

/-- After `s` rounds, exactly the first `s` time slices are present, and each
cell has exactly the symbol produced by the actual recurrence. -/
theorem stage_iff (M : LocalSystem P S d) (hd : 0 < d) (T s : Nat)
    (t : Fin T) (p : P) (a : S) :
    (t, p, a) ∈ stage (operator M T) s ↔ t.val < s ∧ a = run M t.val p := by
  induction s generalizing t p a with
  | zero => simp [stage]
  | succ s ih =>
      change (operator M T (stage (operator M T) s)) (t, p, a) ↔ _
      dsimp only [operator, Set.mem_setOf_eq]
      constructor
      · rintro (⟨ht, ha⟩ | ⟨u, htu, b, hb, ha⟩)
        · change t.val = 0 at ht
          simp only [ht, run]
          exact ⟨Nat.zero_lt_succ s, ha⟩
        · change t.val = u.val + 1 at htu
          have hu := (ih u (M.neighbor p ⟨0, hd⟩) (b ⟨0, hd⟩)).mp (hb ⟨0, hd⟩)
          have hb' : b = fun j => run M u.val (M.neighbor p j) := by
            funext j
            exact ((ih u (M.neighbor p j) (b j)).mp (hb j)).2
          refine ⟨by omega, ?_⟩
          simpa only [htu, run, hb'] using ha
      · rintro ⟨ht, ha⟩
        by_cases ht0 : t.val = 0
        · exact Or.inl ⟨ht0, by simpa only [ht0, run] using ha⟩
        · have huT : t.val - 1 < T := by omega
          let u : Fin T := ⟨t.val - 1, huT⟩
          have htu : t.val = u.val + 1 := by dsimp [u]; omega
          refine Or.inr ⟨u, htu, (fun j => run M u.val (M.neighbor p j)), ?_, ?_⟩
          · intro j
            exact (ih u _ _).mpr ⟨by omega, rfl⟩
          · simpa only [htu, run] using ha

theorem stage_stable (M : LocalSystem P S d) (hd : 0 < d) (T : Nat) :
    stage (operator M T) (T + 1) = stage (operator M T) T := by
  ext ⟨t, p, a⟩
  rw [stage_iff M hd, stage_iff M hd]
  have := t.isLt
  simp [Nat.lt_succ_of_lt this, this]

/-- The least fixed point is the entire bounded computation, with no
spurious symbols. This also handles an empty time domain. -/
theorem leastFixedPoint_iff (M : LocalSystem P S d) (hd : 0 < d) (T : Nat)
    (t : Fin T) (p : P) (a : S) :
    (t, p, a) ∈ leastFixedPoint (operator M T) ↔ a = run M t.val p := by
  rw [← LeastFixedPoints.stage_fixed (operator M T) (operator_monotone M T)
    T (stage_stable M hd T), stage_iff M hd]
  simp [t.isLt]

end Lax751879Proofs.ComputationTableau
