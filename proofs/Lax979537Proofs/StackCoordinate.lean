import Lax979537Proofs.StackCheckedUnary
import Lax979537Proofs.StackCheckBound

namespace Lax979537Proofs.StackCoordinate

open StackProgram StackTransfer

variable {K Aux : Type} [DecidableEq K]

def parse (input coord domain copyLeft copyRight tmp : K) : BitProgram K ((Aux × Bool) × Bool) :=
  .seq (StackCheckedUnary.parse input coord)
    (StackCheckBound.checkBound coord domain copyLeft copyRight tmp)

def result (input coord domain : K) (s : BitStore K ((Aux × Bool) × Bool)) :
    BitStore K ((Aux × Bool) × Bool) :=
  StackCheckBound.result coord domain (StackCheckedUnary.result input coord s)

/-- Read and validate one pointed coordinate. Both domain and parsed
coordinate are retained, and all three comparison work stacks are empty. -/
theorem parse_executes (input coord domain copyLeft copyRight tmp : K)
    (hsep : [input, coord, domain, copyLeft, copyRight, tmp].Nodup)
    (s : BitStore K ((Aux × Bool) × Bool))
    (hc : s.stk coord = []) (hl : s.stk copyLeft = [])
    (hr : s.stk copyRight = []) (ht : s.stk tmp = []) :
    ∃ t, t ≤ 15 * (s.stk input).length + 12 * (s.stk domain).length + 21 ∧
      Executes (parse input coord domain copyLeft copyRight tmp) s (result input coord domain s) t := by
  have hsep' := (List.nodup_cons.mp hsep).2
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true,
    not_or, and_true] at hsep
  have hic : input ≠ coord := by tauto
  let u := StackCheckedUnary.result input coord s
  obtain ⟨a, ha, hp⟩ := StackCheckedUnary.parse_linear_bound input coord hic s
  have hup (key : K) (hi : key ≠ input) (hcoord : key ≠ coord) : u.stk key = s.stk key :=
    StackCheckedUnary.result_preserves input coord key hi hcoord s
  have hul : u.stk copyLeft = [] := by rw [hup _ (by tauto) (by tauto)]; exact hl
  have hur : u.stk copyRight = [] := by rw [hup _ (by tauto) (by tauto)]; exact hr
  have hut : u.stk tmp = [] := by rw [hup _ (by tauto) (by tauto)]; exact ht
  obtain ⟨b, hb, hq⟩ := StackCheckBound.checkBound_executes coord domain copyLeft copyRight tmp
    hsep' u hul hur hut
  have hud : u.stk domain = s.stk domain := hup _ (by tauto) (by tauto)
  have huc : (u.stk coord).length = (StackUnary.splitUnary (s.stk input)).1 := by
    simp [u, StackCheckedUnary.result, hc]
  rw [hud, huc] at hb
  have hcount := StackUnary.splitUnary_le (s.stk input)
  exact ⟨a + b, by omega, Executes.seq hp hq⟩

theorem result_preserves (input coord domain key : K) (hi : key ≠ input) (hc : key ≠ coord)
    (s : BitStore K ((Aux × Bool) × Bool)) :
    (result input coord domain s).stk key = s.stk key :=
  StackCheckedUnary.result_preserves input coord key hi hc s

theorem result_valid (input coord domain : K)
    (hdi : domain ≠ input) (hdc : domain ≠ coord)
    (s : BitStore K ((Aux × Bool) × Bool)) (hc : s.stk coord = []) :
    (result input coord domain s).state.1.2 =
      (s.state.1.2 && (StackUnary.splitUnary (s.stk input)).2.isSome &&
        decide ((StackUnary.splitUnary (s.stk input)).1 < (s.stk domain).length)) := by
  simp [result, StackCheckBound.result, StackCheckedUnary.result, hdi, hdc, hc]

end Lax979537Proofs.StackCoordinate
