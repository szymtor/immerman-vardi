import Lax751879Proofs.StackTransfer

namespace Lax751879Proofs.StackBoolean

open StackProgram StackTransfer

variable {K Aux : Type} [DecidableEq K]

abbrev EvalStore (K Aux : Type) := BitStore K ((Aux × Bool) × Bool)
abbrev EvalProgram (K Aux : Type) := BitProgram K ((Aux × Bool) × Bool)

/-- Evaluators return one Boolean, reset the spare/scratch registers, and
restore every input and private stack. The outer auxiliary state is framed. -/
def result (b : Bool) (s : EvalStore K Aux) : EvalStore K Aux :=
  ⟨(((s.state.1.1.1, true), b), none), s.stk⟩

def Returns (p : EvalProgram K Aux) (s : EvalStore K Aux) (b : Bool) (cost : Nat) : Prop :=
  Executes p s (result b s) cost

def answer (b : Bool) : EvalProgram K Aux :=
  .atom (.load (fun s => (((s.1.1.1, true), b), none)))

def negate : EvalProgram K Aux :=
  .atom (.load (fun s => (((s.1.1.1, true), !s.1.2), none)))

def save (port : K) : EvalProgram K Aux :=
  .atom (.push port (fun s => s.1.2))

def combine (port : K) (op : Bool → Bool → Bool) : EvalProgram K Aux :=
  .atom (.pop port (fun s b => (((s.1.1.1, true), op (b.getD false) s.1.2), none)))

def binary (port : K) (op : Bool → Bool → Bool) (p q : EvalProgram K Aux) : EvalProgram K Aux :=
  .seq p (.seq (save port) (.seq q (combine port op)))

def saved (port : K) (b : Bool) (s : EvalStore K Aux) : EvalStore K Aux :=
  ⟨(result b s).state, Function.update s.stk port (b :: s.stk port)⟩

theorem answer_returns (b : Bool) (s : EvalStore K Aux) : Returns (answer b) s b 1 :=
  Executes.atom _ _

theorem negate_returns {p : EvalProgram K Aux} {s : EvalStore K Aux} {b : Bool} {cost : Nat}
    (h : Returns p s b cost) : Returns (.seq p negate) s (!b) (cost + 1) := by
  exact Executes.seq h (Executes.atom _ _)

theorem combine_saved (port : K) (op : Bool → Bool → Bool) (b d : Bool) (s : EvalStore K Aux) :
    Op.apply (.pop port (fun s : ((Aux × Bool) × Bool) × Option Bool => fun a =>
      (((s.1.1.1, true), op (a.getD false) s.1.2), none))) (result d (saved port b s)) =
      result (op b d) s := by
  apply Store.ext
  · simp [Op.apply, result, saved]
  · simp [Op.apply, result, saved, Function.update_idem]

/-- Boolean composition uses a private stack slot to retain the left
answer. Its previous contents are restored after the right evaluation. -/
theorem binary_returns (port : K) (op : Bool → Bool → Bool)
    {p q : EvalProgram K Aux} {s : EvalStore K Aux} {b d : Bool} {cp cq : Nat}
    (hp : Returns p s b cp) (hq : Returns q (saved port b s) d cq) :
    Returns (binary port op p q) s (op b d) (cp + cq + 2) := by
  have hs : Executes (save port) (result b s) (saved port b s) 1 := Executes.atom _ _
  have hc := Executes.atom
    (.pop port (fun s : ((Aux × Bool) × Bool) × Option Bool => fun a =>
      (((s.1.1.1, true), op (a.getD false) s.1.2), none))) (result d (saved port b s))
  rw [combine_saved] at hc
  have h := Executes.seq hp (Executes.seq hs (Executes.seq hq hc))
  have he : cp + (1 + (cq + 1)) = cp + cq + 2 := by omega
  simpa only [he] using h

end Lax751879Proofs.StackBoolean
