import Lax979537Proofs.NodeClosure

namespace Lax979537Proofs.NodeSupport

open Turing PersistentStack NodeMachine TimedNodes NodeTrace

variable {Node Symbol Initial : Type}

def Known (H : Heap Node Symbol) (p : Option Node) : Prop :=
  ∀ n, p = some n → ∃ a parent, (n, a, parent) ∈ H

def Linked (H : Heap Node Symbol) : Prop :=
  ∀ n a parent, (n, a, parent) ∈ H → Known H parent

def Supported (H : Heap Node Symbol) (S : Set Symbol) : Prop :=
  ∀ n a parent, (n, a, parent) ∈ H → a ∈ S

theorem known_mono {H G : Heap Node Symbol} (h : H ⊆ G) {p : Option Node} (hp : Known H p) :
    Known G p := by
  intro n hn
  obtain ⟨a, parent, hr⟩ := hp n hn
  exact ⟨a, parent, h hr⟩

theorem chain_known {H : Heap Node Symbol} {p : Option Node} {xs : List Symbol}
    (h : Chain H p xs) : Known H p := by
  cases h with
  | nil => intro n hn; cases hn
  | cons hr ht =>
      intro n hn
      cases hn
      exact ⟨_, _, hr⟩

theorem records_linked (xs : List (Node × Symbol)) : Linked (NodeInput.records xs) := by
  induction xs with
  | nil => intro n a p h; exact False.elim h
  | cons x xs ih =>
      intro n a p h
      rcases Set.mem_insert_iff.mp h with he | h
      · cases he
        exact known_mono (Set.subset_insert _ _) (chain_known (NodeInput.records_chain xs))
      · exact known_mono (Set.subset_insert _ _) (ih n a p h)

theorem records_supported (xs : List (Node × Symbol)) (S : Set Symbol)
    (h : ∀ x ∈ xs, x.2 ∈ S) : Supported (NodeInput.records xs) S := by
  induction xs with
  | nil => intro n a p hr; exact False.elim hr
  | cons x xs ih =>
      intro n a p hr
      rcases Set.mem_insert_iff.mp hr with he | hr
      · cases he; exact h x (by simp)
      · exact ih (fun y hy => h y (List.mem_cons_of_mem _ hy)) n a p hr

variable {K Λ State : Type} {Γ : K → Type} [DecidableEq K]

theorem step_linked {M : Λ → TM2.Stmt Γ Λ State} {fresh : Node} {H G : Records Node Γ}
    {c d : NodeMachine.Cfg Γ Λ State Node} (hs : Step M fresh H c G d)
    (hH : Linked H) (hc : ∀ k, Known H (c.heads k)) : Linked G := by
  cases hs with
  | stopped | enter | pop | peek | load | branch | goto | halt => exact hH
  | push k f q v heads =>
      intro n a p hr
      rcases Set.mem_insert_iff.mp hr with he | hr
      · cases he; exact known_mono (Set.subset_insert _ _) (hc k)
      · exact known_mono (Set.subset_insert _ _) (hH n a p hr)

theorem step_supported (tm : FinTM2) {fresh : Node} {H G : Records Node tm.Γ}
    {c d : NodeMachine.Cfg tm.Γ tm.Λ tm.σ Node} (hs : Step tm.m fresh H c G d)
    (hc : c.cursor ∈ TM2MicroSupport.controls tm)
    (hH : Supported H (TM2Alphabet.alphabet tm)) : Supported G (TM2Alphabet.alphabet tm) := by
  cases hs with
  | stopped | enter | pop | peek | load | branch | goto | halt => exact hH
  | push k f q v heads =>
      obtain ⟨l, hl⟩ := (TM2MicroSupport.instruction_mem tm _).mp hc
      have hq := TM2Alphabet.supports_substatement hl (TM2Alphabet.machine_supports tm l)
      intro n a p hr
      rcases Set.mem_insert_iff.mp hr with he | hr
      · cases he; exact hq.1 v
      · exact hH n a p hr

variable (tm : FinTM2) (xs : List (tm.Γ tm.k₀)) (ids : Fin xs.length → Initial)
  (hi : Function.Injective ids)

theorem input_linked : Linked (NodeInput.heap tm xs ids) := records_linked _

theorem input_supported : Supported (NodeInput.heap tm xs ids) (TM2Alphabet.alphabet tm) := by
  classical
  apply records_supported
  intro x hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  simp [TM2Alphabet.alphabet]

theorem snapshot_control (t : Nat) :
    (snapshot (input tm xs ids hi) t).2.cursor ∈ TM2MicroSupport.controls tm := by
  rw [(snapshot_sound (input tm xs ids hi) t).2.2.1]
  exact (TM2MicroSupport.initial_run_support tm xs t).1

theorem snapshot_heads_known (t : Nat) (k : tm.K) :
    Known (snapshot (input tm xs ids hi) t).1 ((snapshot (input tm xs ids hi) t).2.heads k) :=
  chain_known ((snapshot_sound (input tm xs ids hi) t).2.2.2.2 k)

theorem snapshot_linked (t : Nat) : Linked (snapshot (input tm xs ids hi) t).1 := by
  induction t with
  | zero => rw [snapshot_zero]; exact input_linked tm xs ids
  | succ t ih =>
      exact step_linked (snapshot_step (input tm xs ids hi) t) ih (snapshot_heads_known tm xs ids hi t)

theorem snapshot_supported (t : Nat) :
    Supported (snapshot (input tm xs ids hi) t).1 (TM2Alphabet.alphabet tm) := by
  induction t with
  | zero => rw [snapshot_zero]; exact input_supported tm xs ids
  | succ t ih =>
      exact step_supported tm (snapshot_step (input tm xs ids hi) t) (snapshot_control tm xs ids hi t) ih

def Within (t : Nat) (p : Option (TimedNodes.Node Initial)) : Prop :=
  ∀ n, p = some n → Before t n

omit [DecidableEq K] in
theorem known_within {H : Records (TimedNodes.Node Initial) Γ} {t : Nat}
    (hH : Bounded H t) {p : Option (TimedNodes.Node Initial)} (hp : Known H p) : Within t p := by
  intro n hn
  obtain ⟨a, parent, hr⟩ := hp n hn
  exact hH n a parent hr

theorem snapshot_heads_within (t : Nat) (k : tm.K) :
    Within t ((snapshot (input tm xs ids hi) t).2.heads k) :=
  known_within (snapshot_sound (input tm xs ids hi) t).2.1 (snapshot_heads_known tm xs ids hi t k)

/-- Every retained record, including popped nodes, has a supported symbol
and a bounded parent reference. This justifies finite tuple coding of heaps. -/
theorem snapshot_record_support (t : Nat) (n : TimedNodes.Node Initial) (a : Sigma tm.Γ)
    (parent : Option (TimedNodes.Node Initial))
    (hr : (n, a, parent) ∈ (snapshot (input tm xs ids hi) t).1) :
    Before t n ∧ a ∈ TM2Alphabet.alphabet tm ∧ Within t parent :=
  ⟨(snapshot_sound (input tm xs ids hi) t).2.1 n a parent hr,
    snapshot_supported tm xs ids hi t n a parent hr,
    known_within (snapshot_sound (input tm xs ids hi) t).2.1
      (snapshot_linked tm xs ids hi t n a parent hr)⟩

end Lax979537Proofs.NodeSupport
