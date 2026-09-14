import Lax751879Proofs.StackDecoder
import Lax751879.OrderedStructures

namespace Lax751879Proofs.FiniteDecoder

open Lax751879.OrderedStructures StackProgram StackTransfer StackReadRelations

/-- Five reserved ports, a fixed counter pool, relation tables, and free
coordinates. The sum of arities is a convenient bound on each fixed arity. -/
abbrev Port (σ : Vocabulary) (k : Nat) := Fin 5 ⊕ (Fin σ.sum ⊕ (Symbol σ ⊕ Fin k))

def counterPort (σ : Vocabulary) (k : Nat) (i : Fin σ.sum) : Port σ k := .inr (.inl i)
def tablePort (σ : Vocabulary) (k : Nat) (r : Symbol σ) : Port σ k := .inr (.inr (.inl r))
def coordPort (σ : Vocabulary) (k : Nat) (i : Fin k) : Port σ k := .inr (.inr (.inr i))

def work (σ : Vocabulary) (k : Nat) : Workspace (Port σ k) where
  domain := .inl 0
  input := .inl 1
  count := .inl 2
  tmp := .inl 3
  rev := .inl 4
  counters := (List.finRange σ.sum).map (counterPort σ k)
  separate := by simp
  counters_nodup := (List.nodup_finRange _).map (by intro a b h; simpa [counterPort] using h)
  counter_fresh := by
    intro c hm
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hm
    simp [counterPort]

theorem arity_le_sum (σ : Vocabulary) (r : Symbol σ) : σ.get r ≤ σ.sum := by
  induction σ with
  | nil => exact Fin.elim0 r
  | cons a σ ih =>
      refine Fin.cases ?_ (fun i => ?_) r
      · simp
      · have h := ih i
        simpa using h.trans (Nat.le_add_left σ.sum a)

def tables (σ : Vocabulary) (k : Nat) : List (Nat × Port σ k) :=
  (List.finRange σ.length).map (fun r => (σ.get r, tablePort σ k r))

def coords (σ : Vocabulary) (k : Nat) : List (Port σ k) :=
  (List.finRange k).map (coordPort σ k)

def layout (σ : Vocabulary) (k : Nat) : StackDecoder.Layout (Port σ k) where
  work := work σ k
  tables := tables σ k
  coords := coords σ k
  table_keys := by
    simp only [tables, List.map_map, Function.comp_def]
    exact (List.nodup_finRange _).map (by intro a b h; simpa [tablePort] using h)
  coord_keys := (List.nodup_finRange _).map (by intro a b h; simpa [coordPort] using h)
  table_fresh := by
    intro r hm
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hm
    simp [Fresh, work, tablePort, counterPort]
  coord_fresh := by
    intro c hm
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hm
    simp [Fresh, work, coordPort, counterPort]
  arity_bound := by
    intro r hm
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hm
    simpa [work] using arity_le_sum σ i
  disjoint := by
    intro c hc r hr
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hr
    simp [coordPort, tablePort]

abbrev Control := ((Unit × Bool) × Bool) × Option Bool
def initial : Control := ((((), true), true), none)

def program (σ : Vocabulary) (k : Nat) : BitProgram (Port σ k) ((Unit × Bool) × Bool) :=
  StackDecoder.decode (layout σ k)

/-- Concrete finite decoder machine. Its output is retained in designated
internal table/coordinate stacks for the formula evaluator. -/
def decoderMachine (σ : Vocabulary) (k : Nat) : Turing.FinTM2 :=
  machine (program σ k) (work σ k).input (work σ k).input initial

def inputStore (σ : Vocabulary) (k : Nat) (xs : List Bool) : BitStore (Port σ k) ((Unit × Bool) × Bool) :=
  ioStore (work σ k).input initial xs

def cost (σ : Vocabulary) (k N : Nat) : Nat :=
  3 * N + 5 + StackReadRelations.cost (tables σ k) N + k * (27 * N + 21)

theorem eval_costPolynomial (σ : Vocabulary) (k N : Nat) :
    (StackDecoder.costPolynomial (layout σ k)).eval N = cost σ k N := by
  simp [StackDecoder.costPolynomial, layout, coords, cost, StackReadRelations.eval_costPolynomial]

theorem program_executes (σ : Vocabulary) (k : Nat) (xs : List Bool) :
    ∃ t, t ≤ (StackDecoder.costPolynomial (layout σ k)).eval xs.length ∧
      Executes (program σ k) (inputStore σ k xs)
        (StackDecoder.result (layout σ k) (inputStore σ k xs)) t := by
  have h := StackDecoder.decode_executes (layout σ k) (inputStore σ k xs)
    (fun p hp => by
      change p ≠ (work σ k).input at hp
      simp [inputStore, ioStore, hp])
  simpa [inputStore, ioStore, layout] using h

theorem decoder_runs (σ : Vocabulary) (k : Nat) (xs : List Bool) :
    ∃ t, t ≤ cost σ k xs.length ∧
      Nonempty (StateTransition.EvalsToInTime (decoderMachine σ k).step
        (Turing.initList (decoderMachine σ k) xs)
        (some (config none (StackDecoder.result (layout σ k) (inputStore σ k xs)))) t) := by
  obtain ⟨t, ht, he⟩ := program_executes σ k xs
  rw [eval_costPolynomial] at ht
  refine ⟨t, ht, ?_⟩
  exact machine_runs (program σ k) (work σ k).input (work σ k).input initial
    (inputStore σ k xs) (StackDecoder.result (layout σ k) (inputStore σ k xs)) t he

end Lax751879Proofs.FiniteDecoder
