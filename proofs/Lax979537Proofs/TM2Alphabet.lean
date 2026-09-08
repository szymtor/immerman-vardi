import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Finset.Image

namespace Lax979537Proofs.TM2Alphabet

open Turing

variable {K Λ State : Type} {Γ : K → Type}

open scoped Classical in
/-- All symbols a finite statement can push, over all finite control states. -/
noncomputable def symbols [Fintype State] : TM2.Stmt Γ Λ State → Finset (Sigma Γ)
  | .push k f q => (Finset.univ.image (fun v => Sigma.mk k (f v))) ∪ symbols q
  | .peek _ _ q | .pop _ _ q | .load _ q => symbols q
  | .branch _ p q => symbols p ∪ symbols q
  | .goto _ | .halt => ∅

def Supports (S : Set (Sigma Γ)) : TM2.Stmt Γ Λ State → Prop
  | .push k f q => (∀ v, Sigma.mk k (f v) ∈ S) ∧ Supports S q
  | .peek _ _ q | .pop _ _ q | .load _ q => Supports S q
  | .branch _ p q => Supports S p ∧ Supports S q
  | .goto _ | .halt => True

theorem supports_symbols [Fintype State] (q : TM2.Stmt Γ Λ State) (S : Set (Sigma Γ))
    (hS : ∀ a ∈ symbols q, a ∈ S) : Supports S q := by
  classical
  induction q with
  | push k f q ih =>
      exact ⟨fun v => hS _ (by simp [symbols]), ih (fun a ha => hS a (by simp [symbols, ha]))⟩
  | peek k f q ih | pop k f q ih | load f q ih => exact ih hS
  | branch f p q ihp ihq =>
      exact ⟨ihp (fun a ha => hS a (by simp [symbols, ha])), ihq (fun a ha => hS a (by simp [symbols, ha]))⟩
  | goto f | halt => trivial

theorem supports_substatement {S : Set (Sigma Γ)} {p q : TM2.Stmt Γ Λ State}
    (hp : p ∈ TM2.stmts₁ q) (hq : Supports S q) : Supports S p := by
  classical
  induction q with
  | push k f q ih =>
      simp only [TM2.stmts₁, Finset.mem_insert] at hp
      rcases hp with rfl | hp
      · exact hq
      · exact ih hp hq.2
  | peek k f q ih | pop k f q ih | load f q ih =>
      simp only [TM2.stmts₁, Finset.mem_insert] at hp
      rcases hp with rfl | hp
      · exact hq
      · exact ih hp hq
  | branch f q r ihq ihr =>
      simp only [TM2.stmts₁, Finset.mem_insert, Finset.mem_union] at hp
      rcases hp with rfl | hp | hp
      · exact hq
      · exact ihq hp hq.1
      · exact ihr hp hq.2
  | goto f | halt =>
      simp only [TM2.stmts₁, Finset.mem_singleton] at hp
      subst p
      exact hq

def Valid (S : Set (Sigma Γ)) (stk : (k : K) → List (Γ k)) : Prop :=
  ∀ k a, a ∈ stk k → Sigma.mk k a ∈ S

theorem stepAux_valid [DecidableEq K] (S : Set (Sigma Γ)) (q : TM2.Stmt Γ Λ State)
    (hq : Supports S q) (v : State) (stk : (k : K) → List (Γ k)) (hs : Valid S stk) :
    Valid S (TM2.stepAux q v stk).stk := by
  induction q generalizing v stk with
  | push k f q ih =>
      apply ih hq.2
      intro j a ha
      by_cases hj : j = k
      · subst j
        simp only [Function.update_self, List.mem_cons] at ha
        rcases ha with rfl | ha
        · exact hq.1 v
        · exact hs k a ha
      · rw [Function.update_of_ne hj] at ha
        exact hs j a ha
  | peek k f q ih | load f q ih => exact ih hq _ _ hs
  | pop k f q ih =>
      apply ih hq
      intro j a ha
      by_cases hj : j = k
      · subst j
        rw [Function.update_self] at ha
        exact hs k a (List.mem_of_mem_tail ha)
      · rw [Function.update_of_ne hj] at ha
        exact hs j a ha
  | branch f p q ihp ihq =>
      cases hf : f v <;> simp only [TM2.stepAux, hf, cond_false, cond_true]
      · exact ihq hq.2 _ _ hs
      · exact ihp hq.1 _ _ hs
  | goto f | halt => exact hs

open scoped Classical in
/-- A finite alphabet for every symbol reachable by this machine. Only the
input alphabet is assumed finite by FinTM2; internal alphabets may be infinite. -/
noncomputable def alphabet (tm : FinTM2) : Finset (Sigma tm.Γ) :=
  letI := tm.σFin
  letI := tm.Γk₀Fin
  letI := tm.ΛFin
  Finset.univ.image (fun a : tm.Γ tm.k₀ => Sigma.mk tm.k₀ a) ∪
    Finset.univ.biUnion (fun l : tm.Λ => symbols (tm.m l))

theorem machine_supports (tm : FinTM2) (l : tm.Λ) : Supports (alphabet tm : Set (Sigma tm.Γ)) (tm.m l) := by
  classical
  letI := tm.σFin
  letI := tm.Γk₀Fin
  letI := tm.ΛFin
  apply supports_symbols
  intro a ha
  simp only [Finset.mem_coe, alphabet, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]
  exact Or.inr ⟨l, ha⟩

theorem initial_valid (tm : FinTM2) (xs : List (tm.Γ tm.k₀)) :
    Valid (alphabet tm : Set (Sigma tm.Γ)) (initList tm xs).stk := by
  classical
  intro k a ha
  by_cases hk : k = tm.k₀
  · subst k
    simp [alphabet]
  · simp [initList, hk] at ha

theorem step_valid (tm : FinTM2) {c d : tm.Cfg} (h : tm.step c = some d)
    (hc : Valid (alphabet tm : Set (Sigma tm.Γ)) c.stk) :
    Valid (alphabet tm : Set (Sigma tm.Γ)) d.stk := by
  cases c with
  | mk l v stk =>
      cases l with
      | none => simp [FinTM2.step, TM2.step] at h
      | some l =>
          have he : TM2.stepAux (tm.m l) v stk = d := Option.some.inj h
          rw [← he]
          exact stepAux_valid _ _ (machine_supports tm l) v stk hc

theorem iterate_valid (tm : FinTM2) (n : Nat) {c d : tm.Cfg}
    (hc : Valid (alphabet tm : Set (Sigma tm.Γ)) c.stk)
    (h : (fun q : Option tm.Cfg => q.bind tm.step)^[n] (some c) = some d) :
    Valid (alphabet tm : Set (Sigma tm.Γ)) d.stk := by
  induction n generalizing d with
  | zero =>
      have he : c = d := Option.some.inj h
      exact he ▸ hc
  | succ n ih =>
      rw [Function.iterate_succ_apply'] at h
      cases hr : (fun q : Option tm.Cfg => q.bind tm.step)^[n] (some c) with
      | none => simp only [hr, Option.bind_none, reduceCtorEq] at h
      | some e =>
          have hs : tm.step e = some d := by simpa only [hr, Option.bind_some] using h
          exact step_valid tm hs (ih hr)

theorem evals_valid (tm : FinTM2) (xs : List (tm.Γ tm.k₀)) {d : tm.Cfg} {T : Nat}
    (h : StateTransition.EvalsToInTime tm.step (initList tm xs) (some d) T) :
    Valid (alphabet tm : Set (Sigma tm.Γ)) d.stk :=
  iterate_valid tm h.steps (initial_valid tm xs) h.evals_in_steps

/-- Finite tagged symbols available to the forthcoming logical simulation. -/
abbrev Symbol (tm : FinTM2) := ↥(alphabet tm)

noncomputable instance (tm : FinTM2) : Fintype (Symbol tm) := inferInstanceAs (Fintype ↥(alphabet tm))

end Lax979537Proofs.TM2Alphabet
