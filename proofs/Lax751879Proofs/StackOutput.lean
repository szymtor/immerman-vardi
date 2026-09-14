import Lax751879Proofs.StackClear
import Lax751879Proofs.StackBoolean

namespace Lax751879Proofs.StackOutput

open StackProgram StackTransfer StackBoolean

variable {K Aux : Type} [DecidableEq K]

theorem length_op {Γ : K → Type} {State : Type} (o : Op Γ State) (s : Store Γ State) (key : K) :
    ((o.apply s).stk key).length ≤ (s.stk key).length + 1 := by
  cases o with
  | push k f =>
      by_cases h : key = k
      · subst key; simp [Op.apply]
      · simp [Op.apply, h]
  | pop k f =>
      by_cases h : key = k
      · subst key; simp [Op.apply]; omega
      · simp [Op.apply, h]
  | peek k f | load f => simp [Op.apply]

/-- A deliberately coarse space bound, valid also on malformed inputs. -/
theorem length_executes {Γ : K → Type} {State : Type} {p : Program Γ State}
    {s t : Store Γ State} {c : Nat} (h : Executes p s t c) (key : K) :
    (t.stk key).length ≤ (s.stk key).length + c := by
  induction h with
  | atom o s => exact length_op o s key
  | seq _ _ ihp ihq => omega
  | branch_true _ _ ih | branch_false _ _ ih => omega
  | loop_false _ => omega
  | loop_true _ _ _ ihp ihq => omega

def clearPorts : List K → BitProgram K Aux
  | [] => .atom (.load (fun s => (s.1, none)))
  | key :: keys => .seq (StackClear.clear key) (clearPorts keys)

def cleared (keys : List K) (s : BitStore K Aux) : BitStore K Aux :=
  ⟨(s.state.1, none), fun key => if key ∈ keys then [] else s.stk key⟩

theorem clearPorts_executes (keys : List K) (s : BitStore K Aux) (M : Nat)
    (hs : ∀ key, (s.stk key).length ≤ M) :
    ∃ c, c ≤ (2 * M + 2) * keys.length + 1 ∧ Executes (clearPorts keys) s (cleared keys s) c := by
  induction keys generalizing s with
  | nil => exact ⟨1, by simp, by simpa [cleared] using Executes.atom (.load (fun s => (s.1, none))) s⟩
  | cons key keys ih =>
      let u : BitStore K Aux := ⟨(s.state.1, none), Function.update s.stk key []⟩
      have hu : ∀ j, (u.stk j).length ≤ M := by
        intro j
        by_cases hj : j = key
        · subst j; simp [u]
        · simpa [u, hj] using hs j
      obtain ⟨c, hc, hp⟩ := ih u hu
      have he : cleared keys u = cleared (key :: keys) s := by
        apply Store.ext
        · rfl
        · funext j
          by_cases hj : j = key <;> by_cases hm : j ∈ keys <;> simp [cleared, u, hj, hm]
      rw [he] at hp
      refine ⟨2 * (s.stk key).length + 2 + c, ?_, Executes.seq (StackClear.clear_store key s) hp⟩
      have hb := hs key
      simp only [List.length_cons, Nat.mul_succ]
      omega

/-- Clear a fixed set of ports, emit the retained answer, and reset control. -/
def output (keys : List K) (port : K) (initial : ((Aux × Bool) × Bool) × Option Bool) : EvalProgram K Aux :=
  .seq (clearPorts keys)
    (.seq (.atom (.push port (fun s => s.1.2))) (.atom (.load (fun _ => initial))))

theorem output_executes (keys : List K) (hall : ∀ key, key ∈ keys) (port : K)
    (initial : ((Aux × Bool) × Bool) × Option Bool) (s : EvalStore K Aux) (M : Nat)
    (hs : ∀ key, (s.stk key).length ≤ M) :
    ∃ c, c ≤ (2 * M + 2) * keys.length + 3 ∧
      Executes (output keys port initial) s (ioStore port initial [s.state.1.2]) c := by
  obtain ⟨c, hc, hp⟩ := clearPorts_executes keys s M hs
  have hpush := Executes.atom (.push port (fun s : ((Aux × Bool) × Bool) × Option Bool => s.1.2))
    (cleared keys s)
  have hload := Executes.atom (.load (fun _ : ((Aux × Bool) × Bool) × Option Bool => initial))
    (Op.apply (.push port (fun s => s.1.2)) (cleared keys s))
  have he : Op.apply (.load (fun _ : ((Aux × Bool) × Bool) × Option Bool => initial))
      (Op.apply (.push port (fun s => s.1.2)) (cleared keys s)) = ioStore port initial [s.state.1.2] := by
    apply Store.ext
    · rfl
    · funext key
      by_cases h : key = port <;> simp [Op.apply, cleared, ioStore, hall, h]
  rw [he] at hload
  exact ⟨c + (1 + 1), by omega, Executes.seq hp (Executes.seq hpush hload)⟩

end Lax751879Proofs.StackOutput
