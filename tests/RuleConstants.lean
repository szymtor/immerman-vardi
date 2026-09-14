import Lax751879Proofs.RuleConstants
import Mathlib.Data.Fin.VecNotation

open Lax751879.OrderedStructures Lax751879Proofs RuleConstants

namespace RuleConstantsTest

@[reducible] def three : OrderedStructure [] := ⟨3, fun r => Fin.elim0 r⟩

def seed : Template [] 1 2 2 where
  numVars := 1
  guard := .truth
  guard_firstOrder := trivial
  parameters := id
  head := ![1, 2]
  premises := []

/-- The first output coordinate is the bound numeral one; the second is
the free query value. -/
example : (compile seed).holds three (fun _ => 2) ∅ ![1, 2] := by
  rw [compile_holds _ _ (by decide)]
  dsimp only [holds, seed]
  refine ⟨(fun _ => 2), trivial, rfl, ?_, ?_⟩
  · decide
  · simp

example : ¬(compile seed).holds three (fun _ => 2) ∅ ![0, 2] := by
  rw [compile_holds _ _ (by decide)]
  dsimp only [holds, seed]
  rintro ⟨a, _, _, he, _⟩
  have h := congrFun he 0
  change Fin.append (Fin.castLE (by decide : 2 ≤ 3)) a (Fin.castAdd 1 (1 : Fin 2)) = (0 : Fin 3) at h
  rw [Fin.append_left] at h
  exact (by decide : (1 : Fin 3) ≠ 0) h

#print axioms RuleConstants.compile_holds

end RuleConstantsTest
