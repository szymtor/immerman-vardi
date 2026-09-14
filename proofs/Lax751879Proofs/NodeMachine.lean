import Lax751879Proofs.PersistentStack
import Lax751879Proofs.TM2MicroSupport

namespace Lax751879Proofs.NodeMachine

open Turing PersistentStack

variable {K Λ State Node : Type} {Γ : K → Type} [DecidableEq K]

structure Cfg (Γ : K → Type) (Λ State Node : Type) where
  cursor : TM2Micro.Cursor Γ Λ State
  var : State
  heads : K → Option Node

abbrev Records (Node : Type) (Γ : K → Type) := Heap Node (Sigma Γ)

def Represents (H : Records Node Γ) (heads : K → Option Node) (stk : (k : K) → List (Γ k)) : Prop :=
  ∀ k, Chain H (heads k) ((stk k).map (Sigma.mk k))

def expand (c : Cfg Γ Λ State Node) (stk : (k : K) → List (Γ k)) : TM2Micro.Cfg Γ Λ State :=
  ⟨c.cursor, c.var, stk⟩

def Matches (H : Records Node Γ) (c : Cfg Γ Λ State Node) (d : TM2Micro.Cfg Γ Λ State) : Prop :=
  c.cursor = d.cursor ∧ c.var = d.var ∧ Represents H c.heads d.stk

omit [DecidableEq K] in
theorem Matches.expand_eq {H : Records Node Γ} {c : Cfg Γ Λ State Node} {d : TM2Micro.Cfg Γ Λ State}
    (h : Matches H c d) : expand c d.stk = d := by
  cases c with
  | mk cursor v heads =>
      cases d with
      | mk cursor' v' stk =>
          rcases h with ⟨rfl, rfl, _⟩
          rfl

/-- Relational execution using positive node reads. Push freshness is a
global time invariant, not a negative premise of a transition rule. -/
inductive Step (M : Λ → TM2.Stmt Γ Λ State) (fresh : Node) :
    Records Node Γ → Cfg Γ Λ State Node → Records Node Γ → Cfg Γ Λ State Node → Prop
  | stopped (H) (v) (heads) : Step M fresh H ⟨.boundary none, v, heads⟩ H ⟨.boundary none, v, heads⟩
  | enter (H) (l) (v) (heads) : Step M fresh H ⟨.boundary (some l), v, heads⟩ H ⟨.instruction (M l), v, heads⟩
  | push (H) (k) (f : State → Γ k) (q) (v) (heads) :
      Step M fresh H ⟨.instruction (.push k f q), v, heads⟩
        (insert (fresh, Sigma.mk k (f v), heads k) H) ⟨.instruction q, v, Function.update heads k (some fresh)⟩
  | pop (H) (k) (f : State → Option (Γ k) → State) (q) (v) (heads) (a : Option (Γ k)) (parent)
      (hread : Read H (heads k) (a.map (Sigma.mk k)) parent) :
      Step M fresh H ⟨.instruction (.pop k f q), v, heads⟩ H ⟨.instruction q, f v a, Function.update heads k parent⟩
  | peek (H) (k) (f : State → Option (Γ k) → State) (q) (v) (heads) (a : Option (Γ k)) (parent)
      (hread : Read H (heads k) (a.map (Sigma.mk k)) parent) :
      Step M fresh H ⟨.instruction (.peek k f q), v, heads⟩ H ⟨.instruction q, f v a, heads⟩
  | load (H) (f : State → State) (q) (v) (heads) :
      Step M fresh H ⟨.instruction (.load f q), v, heads⟩ H ⟨.instruction q, f v, heads⟩
  | branch (H) (f : State → Bool) (p q) (v) (heads) :
      Step M fresh H ⟨.instruction (.branch f p q), v, heads⟩ H ⟨.instruction (if f v then p else q), v, heads⟩
  | goto (H) (f : State → Λ) (v) (heads) :
      Step M fresh H ⟨.instruction (.goto f), v, heads⟩ H ⟨.boundary (some (f v)), v, heads⟩
  | halt (H) (v) (heads) : Step M fresh H ⟨.instruction .halt, v, heads⟩ H ⟨.boundary none, v, heads⟩

theorem step_sound {M : Λ → TM2.Stmt Γ Λ State} {fresh : Node} {H G : Records Node Γ}
    {c d : Cfg Γ Λ State Node} (h : Step M fresh H c G d)
    (hH : Functional H) (hf : Fresh H fresh) (stk : (k : K) → List (Γ k)) (hs : Represents H c.heads stk) :
    Functional G ∧ Matches G d (TM2Micro.next M (expand c stk)) := by
  cases h with
  | stopped | enter | load | branch | goto | halt => exact ⟨hH, rfl, rfl, hs⟩
  | push k f q v heads =>
      refine ⟨insert_functional hH hf _ _, rfl, rfl, ?_⟩
      intro j
      by_cases hj : j = k
      · subst j
        simpa only [TM2Micro.next, TM2Micro.instruction, expand, Function.update_self, List.map_cons] using
          push_chain (hs k) fresh (Sigma.mk k (f v))
      · simpa only [TM2Micro.next, TM2Micro.instruction, expand, Function.update_of_ne hj] using
          (hs j).mono (Set.subset_insert _ _)
  | pop k f q v heads a parent hread =>
      obtain ⟨ha, ht⟩ := read_map_correct (Sigma.mk k) (fun _ _ he => by simpa using he) hH (hs k) hread
      refine ⟨hH, rfl, ?_, ?_⟩
      · exact congrArg (f v) ha
      · intro j
        by_cases hj : j = k
        · subst j
          simpa only [TM2Micro.next, TM2Micro.instruction, expand, Function.update_self] using ht
        · simpa only [TM2Micro.next, TM2Micro.instruction, expand, Function.update_of_ne hj] using hs j
  | peek k f q v heads a parent hread =>
      have ha := (read_map_correct (Sigma.mk k) (fun _ _ he => by simpa using he) hH (hs k) hread).1
      exact ⟨hH, rfl, congrArg (f v) ha, hs⟩

theorem step_exists (M : Λ → TM2.Stmt Γ Λ State) (fresh : Node) (H : Records Node Γ)
    (c : Cfg Γ Λ State Node) (stk : (k : K) → List (Γ k)) (hs : Represents H c.heads stk) :
    ∃ G d, Step M fresh H c G d := by
  cases c with
  | mk cursor v heads =>
      cases cursor with
      | boundary l =>
          cases l with
          | none => exact ⟨_, _, .stopped H v heads⟩
          | some l => exact ⟨_, _, .enter H l v heads⟩
      | instruction q =>
          cases q with
          | push k f q => exact ⟨_, _, .push H k f q v heads⟩
          | pop k f q =>
              obtain ⟨parent, hr, _⟩ := (hs k).read_exists
              exact ⟨_, _, .pop H k f q v heads (stk k).head? parent (by simpa only [List.head?_map] using hr)⟩
          | peek k f q =>
              obtain ⟨parent, hr, _⟩ := (hs k).read_exists
              exact ⟨_, _, .peek H k f q v heads (stk k).head? parent (by simpa only [List.head?_map] using hr)⟩
          | load f q => exact ⟨_, _, .load H f q v heads⟩
          | branch f p q => exact ⟨_, _, .branch H f p q v heads⟩
          | goto f => exact ⟨_, _, .goto H f v heads⟩
          | halt => exact ⟨_, _, .halt H v heads⟩

theorem step_subset {M : Λ → TM2.Stmt Γ Λ State} {fresh : Node} {H G : Records Node Γ}
    {c d : Cfg Γ Λ State Node} (h : Step M fresh H c G d) : H ⊆ G := by
  cases h with
  | push => exact Set.subset_insert _ _
  | stopped | enter | pop | peek | load | branch | goto | halt => exact Set.Subset.refl _

theorem step_mono {M : Λ → TM2.Stmt Γ Λ State} {fresh : Node} {H G J : Records Node Γ}
    {c d : Cfg Γ Λ State Node} (h : Step M fresh H c G d) (hHJ : H ⊆ J) :
    ∃ J', Step M fresh J c J' d ∧ G ⊆ J' := by
  cases h with
  | stopped => exact ⟨_, .stopped _ _ _, hHJ⟩
  | enter => exact ⟨_, .enter _ _ _ _, hHJ⟩
  | push k f q v heads => exact ⟨_, .push _ _ _ _ _ _, Set.insert_subset_insert hHJ⟩
  | pop k f q v heads a parent hread => exact ⟨_, .pop _ _ _ _ _ _ _ _ (hread.mono hHJ), hHJ⟩
  | peek k f q v heads a parent hread => exact ⟨_, .peek _ _ _ _ _ _ _ _ (hread.mono hHJ), hHJ⟩
  | load => exact ⟨_, .load _ _ _ _ _, hHJ⟩
  | branch => exact ⟨_, .branch _ _ _ _ _ _, hHJ⟩
  | goto => exact ⟨_, .goto _ _ _ _, hHJ⟩
  | halt => exact ⟨_, .halt _ _ _, hHJ⟩

theorem step_unique {M : Λ → TM2.Stmt Γ Λ State} {fresh : Node} {H G J : Records Node Γ}
    {c d e : Cfg Γ Λ State Node} (hF : Functional H)
    (hd : Step M fresh H c G d) (he : Step M fresh H c J e) : G = J ∧ d = e := by
  cases hd with
  | stopped | enter | push | load | branch | goto | halt => cases he; exact ⟨rfl, rfl⟩
  | pop k f q v heads a parent hr =>
      cases he with
      | pop _ _ _ _ _ b other hs =>
          obtain ⟨ha, hp⟩ := read_unique hF hr hs
          have hab : a = b := Option.map_injective (fun _ _ h => by simpa using h) ha
          cases hab; cases hp
          exact ⟨rfl, rfl⟩
  | peek k f q v heads a parent hr =>
      cases he with
      | peek _ _ _ _ _ b other hs =>
          have ha := (read_unique hF hr hs).1
          have hab : a = b := Option.map_injective (fun _ _ h => by simpa using h) ha
          cases hab
          exact ⟨rfl, rfl⟩

def added (fresh : Node) (c : Cfg Γ Λ State Node) : Option (Node × Sigma Γ × Option Node) :=
  match c.cursor with
  | .instruction (.push k f _) => some (fresh, Sigma.mk k (f c.var), c.heads k)
  | _ => none

theorem step_records {M : Λ → TM2.Stmt Γ Λ State} {fresh : Node} {H G : Records Node Γ}
    {c d : Cfg Γ Λ State Node} (h : Step M fresh H c G d) (r : Node × Sigma Γ × Option Node) :
    r ∈ G ↔ r ∈ H ∨ added fresh c = some r := by
  cases h <;> simp [added, eq_comm, or_comm]

end Lax751879Proofs.NodeMachine
