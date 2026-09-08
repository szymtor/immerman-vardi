import Lax979537Proofs.TM2Alphabet
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Lax979537Proofs.TM2Micro

open Turing

variable {K Λ State : Type} {Γ : K → Type} [DecidableEq K]

inductive Cursor (Γ : K → Type) (Λ State : Type)
  | boundary (label : Option Λ)
  | instruction (stmt : TM2.Stmt Γ Λ State)

structure Cfg (Γ : K → Type) (Λ State : Type) where
  cursor : Cursor Γ Λ State
  var : State
  stk : (k : K) → List (Γ k)

def boundary (c : TM2.Cfg Γ Λ State) : Cfg Γ Λ State := ⟨.boundary c.l, c.var, c.stk⟩

def instruction (q : TM2.Stmt Γ Λ State) (v : State) (stk : (k : K) → List (Γ k)) : Cfg Γ Λ State :=
  ⟨.instruction q, v, stk⟩

/-- One explicit operation per transition, with an absorbing halt boundary. -/
def next (M : Λ → TM2.Stmt Γ Λ State) (c : Cfg Γ Λ State) : Cfg Γ Λ State :=
  match c.cursor with
  | .boundary none => c
  | .boundary (some l) => instruction (M l) c.var c.stk
  | .instruction q => match q with
    | .push k f q => instruction q c.var (Function.update c.stk k (f c.var :: c.stk k))
    | .pop k f q => instruction q (f c.var (c.stk k).head?) (Function.update c.stk k (c.stk k).tail)
    | .peek k f q => instruction q (f c.var (c.stk k).head?) c.stk
    | .load f q => instruction q (f c.var) c.stk
    | .branch f p q => instruction (if f c.var then p else q) c.var c.stk
    | .goto f => ⟨.boundary (some (f c.var)), c.var, c.stk⟩
    | .halt => ⟨.boundary none, c.var, c.stk⟩

def weight : TM2.Stmt Γ Λ State → Nat
  | .push _ _ q | .pop _ _ q | .peek _ _ q | .load _ q => weight q + 1
  | .branch _ p q => max (weight p) (weight q) + 1
  | .goto _ | .halt => 1

/-- Executing one statement by individual operations agrees with the
original macro-step, with a bound depending only on statement syntax. -/
theorem statement_refines (M : Λ → TM2.Stmt Γ Λ State) (q : TM2.Stmt Γ Λ State)
    (v : State) (stk : (k : K) → List (Γ k)) :
    ∃ t, t ≤ weight q ∧ (next M)^[t] (instruction q v stk) = boundary (TM2.stepAux q v stk) := by
  induction q generalizing v stk with
  | push k f q ih | pop k f q ih | peek k f q ih | load f q ih =>
      obtain ⟨t, ht, hp⟩ := ih _ _
      exact ⟨t + 1, Nat.add_le_add_right ht 1, by simpa only [Function.iterate_succ_apply, next, instruction, TM2.stepAux] using hp⟩
  | branch f p q ihp ihq =>
      cases hf : f v with
      | false =>
          obtain ⟨t, ht, hp⟩ := ihq v stk
          refine ⟨t + 1, Nat.add_le_add_right (ht.trans (Nat.le_max_right _ _)) 1, ?_⟩
          simpa [Function.iterate_succ_apply, next, instruction, TM2.stepAux, hf] using hp
      | true =>
          obtain ⟨t, ht, hp⟩ := ihp v stk
          refine ⟨t + 1, Nat.add_le_add_right (ht.trans (Nat.le_max_left _ _)) 1, ?_⟩
          simpa [Function.iterate_succ_apply, next, instruction, TM2.stepAux, hf] using hp
  | goto f | halt => exact ⟨1, le_rfl, rfl⟩

def macroNext (M : Λ → TM2.Stmt Γ Λ State) (c : TM2.Cfg Γ Λ State) : TM2.Cfg Γ Λ State :=
  (TM2.step M c).getD c

theorem macro_refines (M : Λ → TM2.Stmt Γ Λ State) (C : Nat)
    (hC : ∀ l, weight (M l) + 1 ≤ C) (c : TM2.Cfg Γ Λ State) :
    ∃ t, t ≤ C ∧ (next M)^[t] (boundary c) = boundary (macroNext M c) := by
  cases c with
  | mk l v stk =>
      cases l with
      | none => exact ⟨0, Nat.zero_le _, rfl⟩
      | some l =>
          obtain ⟨t, ht, hp⟩ := statement_refines M (M l) v stk
          refine ⟨t + 1, (Nat.add_le_add_right ht 1).trans (hC l), ?_⟩
          simpa only [Function.iterate_succ_apply, next, boundary, macroNext, TM2.step, Option.getD_some] using hp

theorem iterate_refines (M : Λ → TM2.Stmt Γ Λ State) (C : Nat)
    (hC : ∀ l, weight (M l) + 1 ≤ C) (n : Nat) (c : TM2.Cfg Γ Λ State) :
    ∃ t, t ≤ C * n ∧ (next M)^[t] (boundary c) = boundary ((macroNext M)^[n] c) := by
  induction n with
  | zero => exact ⟨0, by simp, rfl⟩
  | succ n ih =>
      obtain ⟨t, ht, hp⟩ := ih
      obtain ⟨u, hu, hq⟩ := macro_refines M C hC ((macroNext M)^[n] c)
      refine ⟨u + t, ?_, ?_⟩
      · rw [Nat.mul_succ]; omega
      · rw [Function.iterate_add_apply, hp, hq, Function.iterate_succ_apply']

noncomputable def factor (tm : FinTM2) : Nat :=
  letI := tm.ΛFin
  (Finset.univ.sum fun l : tm.Λ => weight (tm.m l)) + 1

theorem weight_le_factor (tm : FinTM2) (l : tm.Λ) : weight (tm.m l) + 1 ≤ factor tm := by
  classical
  letI := tm.ΛFin
  change weight (tm.m l) + 1 ≤ (Finset.univ.sum fun j : tm.Λ => weight (tm.m j)) + 1
  exact Nat.add_le_add_right
    (Finset.single_le_sum (fun j _ => Nat.zero_le (weight (tm.m j))) (Finset.mem_univ l)) 1

theorem finite_iterate_refines (tm : FinTM2) (n : Nat) (c : tm.Cfg) :
    ∃ t, t ≤ factor tm * n ∧
      (next tm.m)^[t] (boundary c) = boundary ((macroNext tm.m)^[n] c) :=
  iterate_refines tm.m (factor tm) (weight_le_factor tm) n c

theorem macro_matches (M : Λ → TM2.Stmt Γ Λ State) (n : Nat) {c d : TM2.Cfg Γ Λ State}
    (h : (fun q : Option (TM2.Cfg Γ Λ State) => q.bind (TM2.step M))^[n] (some c) = some d) :
    (macroNext M)^[n] c = d := by
  induction n generalizing c with
  | zero => exact Option.some.inj h
  | succ n ih =>
      rw [Function.iterate_succ_apply] at h ⊢
      cases hs : TM2.step M c with
      | none =>
          have hn : (fun q : Option (TM2.Cfg Γ Λ State) => q.bind (TM2.step M))^[n] none = none :=
            Function.iterate_fixed rfl n
          simp only [Option.bind_some, hs, hn, reduceCtorEq] at h
      | some e =>
          have he : (fun q : Option (TM2.Cfg Γ Λ State) => q.bind (TM2.step M))^[n] (some e) = some d := by
            simpa only [Option.bind_some, hs] using h
          simpa only [macroNext, hs, Option.getD_some] using ih he

/-- Bounded actual TM2 runs are reproduced with only a fixed multiplicative
overhead. No step-count composition assertion is assumed. -/
theorem evals_refines (tm : FinTM2) {c d : tm.Cfg} {T : Nat}
    (h : StateTransition.EvalsToInTime tm.step c (some d) T) :
    ∃ t, t ≤ factor tm * T ∧ (next tm.m)^[t] (boundary c) = boundary d := by
  obtain ⟨t, ht, hp⟩ := finite_iterate_refines tm h.steps c
  rw [macro_matches tm.m h.steps h.evals_in_steps] at hp
  exact ⟨t, ht.trans (Nat.mul_le_mul_left _ h.steps_le_m), hp⟩

theorem halt_fixed (M : Λ → TM2.Stmt Γ Λ State) (c : TM2.Cfg Γ Λ State) (hc : c.l = none) :
    next M (boundary c) = boundary c := by
  simp [next, boundary, hc]

/-- After a bounded halting computation, any larger time gives the same
terminal configuration. This permits a coarse tuple-sized time horizon. -/
theorem evals_at_time (tm : FinTM2) {c d : tm.Cfg} {T N : Nat}
    (h : StateTransition.EvalsToInTime tm.step c (some d) T) (hd : d.l = none)
    (hN : factor tm * T ≤ N) : (next tm.m)^[N] (boundary c) = boundary d := by
  obtain ⟨t, ht, hp⟩ := evals_refines tm h
  have htn : t ≤ N := ht.trans hN
  rw [show N = (N - t) + t from (Nat.sub_add_cancel htn).symm,
    Function.iterate_add_apply, hp]
  exact Function.iterate_fixed (halt_fixed tm.m d hd) _

end Lax979537Proofs.TM2Micro
