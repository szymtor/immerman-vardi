import Lax979537Proofs.StackReadTable

namespace Lax979537Proofs.StackReadRelations

open StackProgram StackTransfer

variable {K Aux : Type} [DecidableEq K]

/-- A fixed finite collection of decoder work stacks. Relation tables live
outside this collection and retain their contents between parsing steps. -/
structure Workspace (K : Type) where
  domain : K
  input : K
  count : K
  tmp : K
  rev : K
  counters : List K
  separate : [domain, input, count, tmp, rev].Nodup
  counters_nodup : counters.Nodup
  counter_fresh : ∀ c ∈ counters, c ∉ [domain, input, count, tmp, rev]

def Fresh (w : Workspace K) (table : K) : Prop :=
  table ∉ [w.domain, w.input, w.count, w.tmp, w.rev] ∧ table ∉ w.counters

def Ready (w : Workspace K) (n : Nat) (s : BitStore K (Aux × Bool)) : Prop :=
  s.stk w.domain = List.replicate n true ∧ s.stk w.tmp = [] ∧ s.stk w.count = [] ∧
    s.stk w.rev = [] ∧ ∀ c ∈ w.counters, s.stk c = []

def oneTable (w : Workspace K) (arity : Nat) (table : K) : BitProgram K (Aux × Bool) :=
  StackReadTable.readTable w.domain w.input table w.count w.tmp w.rev (w.counters.take arity)

theorem oneTable_executes (w : Workspace K) (arity : Nat) (table : K)
    (hbound : arity ≤ w.counters.length) (hf : Fresh w table)
    (n : Nat) (s : BitStore K (Aux × Bool)) (hs : Ready w n s) (ht : s.stk table = []) :
    ∃ t, t ≤ (StackReadTable.costPolynomial arity).eval n ∧
      Executes (oneTable w arity table) s (StackReadTable.result w.input table n arity s) t := by
  have hcore := w.separate
  have htable := hf.1
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true,
    not_or, and_true] at hcore htable
  have hslots : ∀ c ∈ w.counters.take arity, c ≠ w.domain ∧ c ≠ w.count ∧ c ≠ w.tmp := by
    intro c hm
    have h := w.counter_fresh c (List.mem_of_mem_take hm)
    simp only [List.mem_cons, List.not_mem_nil, not_false_eq_true, not_or, and_true] at h
    tauto
  have h := StackReadTable.readTable_executes w.domain w.input table w.count w.tmp w.rev
    (by tauto) (by tauto) (by tauto) (by tauto) (by tauto)
    (by tauto) (by tauto) (by tauto)
    (w.counters.take arity) w.counters_nodup.take hslots n s
    hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1 ht
    (fun c hm => hs.2.2.2.2 c (List.mem_of_mem_take hm))
  simpa only [List.length_take, Nat.min_eq_left hbound] using h

theorem result_ready (w : Workspace K) (table : K) (hf : Fresh w table)
    (n arity : Nat) (s : BitStore K (Aux × Bool)) (hs : Ready w n s) :
    Ready w n (StackReadTable.result w.input table n arity s) := by
  have hcore := w.separate
  have htable := hf.1
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true,
    not_or, and_true] at hcore htable
  have hp (c : K) (hi : c ≠ w.input) (ht : c ≠ table) :
      (StackReadTable.result w.input table n arity s).stk c = s.stk c :=
    StackReadTable.result_preserves _ _ _ hi ht _ _ _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hp w.domain (by tauto) (by tauto)]; exact hs.1
  · rw [hp w.tmp (by tauto) (by tauto)]; exact hs.2.1
  · rw [hp w.count (by tauto) (by tauto)]; exact hs.2.2.1
  · rw [hp w.rev (by tauto) (by tauto)]; exact hs.2.2.2.1
  · intro c hm
    have h := w.counter_fresh c hm
    simp only [List.mem_cons, List.not_mem_nil, not_false_eq_true, not_or, and_true] at h
    have hct : c ≠ table := fun he => hf.2 (he ▸ hm)
    rw [hp c (by tauto) hct]
    exact hs.2.2.2.2 c hm

def readTables (w : Workspace K) : List (Nat × K) → BitProgram K (Aux × Bool)
  | [] => .atom (.load (fun s => (s.1, none)))
  | (arity, table) :: rest => .seq (oneTable w arity table) (readTables w rest)

def result (w : Workspace K) (n : Nat) : List (Nat × K) →
    BitStore K (Aux × Bool) → BitStore K (Aux × Bool)
  | [], s => ⟨(s.state.1, none), s.stk⟩
  | (arity, table) :: rest, s =>
      result w n rest (StackReadTable.result w.input table n arity s)

noncomputable def costPolynomial : List (Nat × K) → Polynomial Nat
  | [] => Polynomial.C 1
  | (arity, _) :: rest => StackReadTable.costPolynomial arity + costPolynomial rest

/-- Parse every table of a fixed vocabulary. The work stacks are reused;
the runtime is a fixed sum of polynomials, including malformed inputs. -/
theorem readTables_executes (w : Workspace K) (tables : List (Nat × K))
    (hkeys : (tables.map Prod.snd).Nodup)
    (hf : ∀ r ∈ tables, Fresh w r.2)
    (hbound : ∀ r ∈ tables, r.1 ≤ w.counters.length)
    (n : Nat) (s : BitStore K (Aux × Bool)) (hs : Ready w n s)
    (hempty : ∀ r ∈ tables, s.stk r.2 = []) :
    ∃ t, t ≤ (costPolynomial tables).eval n ∧
      Executes (readTables w tables) s (result w n tables s) t := by
  induction tables generalizing s with
  | nil => exact ⟨1, by simp [costPolynomial], Executes.atom _ _⟩
  | cons r rest ih =>
      obtain ⟨arity, table⟩ := r
      obtain ⟨hnot, hkeys'⟩ := List.nodup_cons.mp hkeys
      have hft := hf (arity, table) (by simp)
      obtain ⟨a, ha, hx⟩ := oneTable_executes w arity table
        (hbound (arity, table) (by simp)) hft n s hs (hempty (arity, table) (by simp))
      let u := StackReadTable.result w.input table n arity s
      have hu : Ready w n u := result_ready w table hft n arity s hs
      have hrest : ∀ r ∈ rest, u.stk r.2 = [] := by
        intro r hm
        have hfr := (hf r (by simp [hm])).1
        simp only [List.mem_cons, List.not_mem_nil, not_false_eq_true, not_or, and_true] at hfr
        have hne : r.2 ≠ table := by
          intro he
          apply hnot
          exact List.mem_map.mpr ⟨r, hm, he⟩
        rw [StackReadTable.result_preserves w.input table r.2 (by tauto) hne]
        exact hempty r (by simp [hm])
      obtain ⟨b, hb, hy⟩ := ih hkeys' (fun r hm => hf r (by simp [hm]))
        (fun r hm => hbound r (by simp [hm])) u hu hrest
      refine ⟨a + b, ?_, Executes.seq hx hy⟩
      simpa only [costPolynomial, Polynomial.eval_add] using Nat.add_le_add ha hb

end Lax979537Proofs.StackReadRelations
