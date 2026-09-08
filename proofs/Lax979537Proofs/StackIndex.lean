import Lax979537Proofs.StackHorner

namespace Lax979537Proofs.StackIndex

open StackProgram StackTransfer StackHorner

variable {K Aux : Type} [DecidableEq K]

def build (domain index counter tmp : K) : List K → BitProgram K Aux
  | [] => .atom (.load (fun s => (s.1, none)))
  | coord :: rest => .seq (step domain index counter tmp coord) (build domain index counter tmp rest)

def value (n : Nat) (coords : List K) (v : K → Nat) (a : Nat) : Nat :=
  coords.foldl (fun a coord => n * a + v coord) a

def budget (n : Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => (7 * n + 9) + (n + 1) * budget n k

noncomputable def costPolynomial : Nat → Polynomial Nat
  | 0 => 1
  | k + 1 => (7 * Polynomial.X + 9) + (Polynomial.X + 1) * costPolynomial k

theorem eval_costPolynomial (n k : Nat) : (costPolynomial k).eval n = budget n k := by
  induction k with
  | zero => simp [costPolynomial, budget]
  | succ k ih => simp [costPolynomial, budget, ih]

/-- Build a unary tuple address by fixed Horner steps. Coordinate ports
may repeat. Inputs and workspace are restored, except for the index result.
The bound is polynomial in n at each fixed tuple arity. -/
theorem build_executes (domain index counter tmp : K) (coords : List K)
    (hsep : [domain, index, counter, tmp].Nodup)
    (hfresh : ∀ coord ∈ coords, coord ∉ [index, counter, tmp])
    (n : Nat) (v : K → Nat) (hbound : ∀ coord ∈ coords, v coord ≤ n)
    (a : Nat) (s : BitStore K Aux) (hdomain : s.stk domain = List.replicate n true)
    (hindex : s.stk index = List.replicate a true)
    (hcoords : ∀ coord ∈ coords, s.stk coord = List.replicate (v coord) true)
    (hcounter : s.stk counter = []) (htmp : s.stk tmp = []) :
    ∃ c, c ≤ (a + 1) * budget n coords.length ∧
      Executes (build domain index counter tmp coords) s (setIndex s index (value n coords v a)) c := by
  induction coords generalizing s a with
  | nil =>
      refine ⟨1, by simp [budget], ?_⟩
      have h := Executes.atom (.load (fun q : Aux × Option Bool => (q.1, none))) s
      simpa [build, value, setIndex, ← hindex] using h
  | cons coord coords ih =>
      have hcoord := hfresh coord (by simp)
      have hv := hbound coord (by simp)
      obtain ⟨c, hc, hp⟩ := step_executes domain index counter tmp coord hsep hcoord n a (v coord) s
        hdomain hindex (hcoords coord (by simp)) hcounter htmp
      have hdi : domain ≠ index := by
        simp only [List.nodup_cons, List.mem_cons, not_or] at hsep
        tauto
      have hci : counter ≠ index := by
        simp only [List.nodup_cons, List.mem_cons, not_or] at hsep
        tauto
      have hti : tmp ≠ index := by
        simp only [List.nodup_cons, List.mem_cons, not_or] at hsep
        tauto
      obtain ⟨d, hd, hq⟩ := ih
        (fun coord hm => hfresh coord (by simp [hm]))
        (fun coord hm => hbound coord (by simp [hm])) (n * a + v coord) (setIndex s index (n * a + v coord))
        (by simp [setIndex, hdi, hdomain]) (by simp [setIndex])
        (by
          intro key hm
          have hi : key ≠ index := by
            have hf := hfresh key (by simp [hm])
            simp only [List.mem_cons, not_or] at hf
            exact hf.1
          simp [setIndex, hi, hcoords key (by simp [hm])])
        (by simp [setIndex, hci, hcounter]) (by simp [setIndex, hti, htmp])
      have he : setIndex (setIndex s index (n * a + v coord)) index
          (value n coords v (n * a + v coord)) = setIndex s index (value n (coord :: coords) v a) := by
        simp [setIndex, value, Function.update_idem]
      rw [he] at hq
      refine ⟨c + d, ?_, Executes.seq hp hq⟩
      have hc' : c ≤ (a + 1) * (7 * n + 9) := by
        calc
          c ≤ (7 * n + 9) * a + 7 * v coord + 8 := hc
          _ ≤ (7 * n + 9) * a + (7 * n + 9) := by omega
          _ = (a + 1) * (7 * n + 9) := by ring
      have hv' : n * a + v coord + 1 ≤ (a + 1) * (n + 1) := by
        simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
        rw [Nat.mul_comm a n]
        omega
      calc
        c + d ≤ (a + 1) * (7 * n + 9) + ((a + 1) * (n + 1)) * budget n coords.length :=
          Nat.add_le_add hc' (hd.trans (Nat.mul_le_mul_right _ hv'))
        _ = (a + 1) * budget n (coord :: coords).length := by simp [budget]; ring

end Lax979537Proofs.StackIndex
