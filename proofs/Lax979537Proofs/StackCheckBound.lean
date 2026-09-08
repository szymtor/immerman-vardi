import Lax979537Proofs.StackCompare
import Lax979537Proofs.StackCopy

namespace Lax979537Proofs.StackCheckBound

open StackProgram StackTransfer

variable {K Aux : Type} [DecidableEq K]

def save : BitProgram K ((Aux × Bool) × Bool) :=
  .atom (.load (fun s => (((s.1.1.1, s.1.2), true), none)))

def restore : BitProgram K ((Aux × Bool) × Bool) :=
  .atom (.load (fun s => (((s.1.1.1, true), s.1.1.2 && s.1.2), none)))

/-- Test one unary coordinate against the domain size, preserving both
arguments and accumulating validity. The spare control bit is reset to true. -/
def checkBound (left right copyLeft copyRight tmp : K) : BitProgram K ((Aux × Bool) × Bool) :=
  .seq save (.seq (StackCopy.copy left copyLeft tmp)
    (.seq (StackCopy.copy right copyRight tmp)
      (.seq (StackCompare.less copyLeft copyRight) restore)))

def result (left right : K) (s : BitStore K ((Aux × Bool) × Bool)) :
    BitStore K ((Aux × Bool) × Bool) :=
  ⟨(((s.state.1.1.1, true), s.state.1.2 && decide ((s.stk left).length < (s.stk right).length)),
    none), s.stk⟩

theorem checkBound_executes (left right copyLeft copyRight tmp : K)
    (hsep : [left, right, copyLeft, copyRight, tmp].Nodup)
    (s : BitStore K ((Aux × Bool) × Bool))
    (hl : s.stk copyLeft = []) (hr : s.stk copyRight = []) (ht : s.stk tmp = []) :
    ∃ t, t ≤ 12 * ((s.stk left).length + (s.stk right).length) + 18 ∧
      Executes (checkBound left right copyLeft copyRight tmp) s (result left right s) t := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true,
    not_or, and_true] at hsep
  have hll : left ≠ copyLeft := by tauto
  have hlt : left ≠ tmp := by tauto
  have hlct : copyLeft ≠ tmp := by tauto
  have hrr : right ≠ copyRight := by tauto
  have hrt : right ≠ tmp := by tauto
  have hrct : copyRight ≠ tmp := by tauto
  have hrl : right ≠ copyLeft := by tauto
  have hcc : copyLeft ≠ copyRight := by tauto
  let u : BitStore K ((Aux × Bool) × Bool) :=
    ⟨(((s.state.1.1.1, s.state.1.2), true), none), s.stk⟩
  let v : BitStore K ((Aux × Bool) × Bool) :=
    ⟨u.state, Function.update s.stk copyLeft (s.stk left)⟩
  let z : BitStore K ((Aux × Bool) × Bool) :=
    ⟨u.state, Function.update (Function.update s.stk copyLeft (s.stk left)) copyRight (s.stk right)⟩
  have hsave : Executes (save : BitProgram K ((Aux × Bool) × Bool)) s u 1 := Executes.atom _ _
  have hcopyL : Executes (StackCopy.copy left copyLeft tmp) u v (7 * (s.stk left).length + 4) := by
    simpa [u, v, hl] using StackCopy.copy_store left copyLeft tmp hll hlt hlct u ht
  have hvt : v.stk tmp = [] := by simp [v, Ne.symm hlct, ht]
  have hcopyR : Executes (StackCopy.copy right copyRight tmp) v z (7 * (s.stk right).length + 4) := by
    simpa [u, v, z, hrl, Ne.symm hcc, hr] using
      StackCopy.copy_store right copyRight tmp hrr hrt hrct v hvt
  let q : BitStore K ((Aux × Bool) × Bool) :=
    ⟨(((s.state.1.1.1, s.state.1.2),
      decide ((s.stk left).length < (s.stk right).length)), none), s.stk⟩
  obtain ⟨a, ha, hcompare⟩ := StackCompare.less_store copyLeft copyRight hcc z
  have hzl : z.stk copyLeft = s.stk left := by simp [z, hcc]
  have hzr : z.stk copyRight = s.stk right := by simp [z]
  rw [hzl, hzr] at ha hcompare
  have he : (⟨((z.state.1.1, decide ((s.stk left).length < (s.stk right).length)), none),
      Function.update (Function.update z.stk copyLeft []) copyRight []⟩ :
      BitStore K ((Aux × Bool) × Bool)) = q := by
    apply Store.ext
    · rfl
    · funext k
      by_cases hkl : k = copyLeft
      · subst k; simp [z, q, hcc, hl]
      · by_cases hkr : k = copyRight
        · subst k; simp [z, q, hr]
        · simp [z, q, hkl, hkr]
  rw [he] at hcompare
  have hrestore : Executes (restore : BitProgram K ((Aux × Bool) × Bool)) q (result left right s) 1 :=
    Executes.atom _ _
  refine ⟨1 + ((7 * (s.stk left).length + 4) +
    ((7 * (s.stk right).length + 4) + (a + 1))), ?_,
    Executes.seq hsave (Executes.seq hcopyL (Executes.seq hcopyR (Executes.seq hcompare hrestore)))⟩
  omega

end Lax979537Proofs.StackCheckBound
