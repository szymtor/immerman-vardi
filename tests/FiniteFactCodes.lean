import Lax751879Proofs.TraceCodes
import Lax751879Proofs.ParameterizedRules
import Mathlib.Data.Fin.VecNotation

open Lax751879Proofs

namespace FiniteFactCodesTest

def initial (p : Fin 2) : Fin 1 → Fin 3 := fun _ => Fin.castLE (by decide) p

def ptr (p : Option (TimedNodes.Node (Fin 2))) : Fin 3 → Fin 3 :=
  NodeCodes.code (d := 2) (w := 2) (by decide) initial p

example : ptr none = ![0, 0, 0] := by decide
example : ptr (some (.inl 1)) = ![1, 1, 0] := by decide
example : ptr (some (.inr 8)) = ![2, 2, 2] := by decide

/-- The final valid timestamp uses the full base-three two-coordinate clock. -/
example : NodeSupport.Within (3 ^ 2) (some (Sum.inr 8 : TimedNodes.Node (Fin 2))) := by
  intro n hn
  cases hn
  change 8 < 3 ^ 2
  decide

example {p q : Option (TimedNodes.Node (Fin 2))}
    (hp : NodeSupport.Within (3 ^ 2) p) (hq : NodeSupport.Within (3 ^ 2) q)
    (he : ptr p = ptr q) : p = q := by
  apply NodeCodes.code_injective (by decide) initial ?_ (by decide) (by decide) hp hq he
  intro p q he
  exact Fin.ext (congrArg (fun x : Fin 3 => x.val) (congrFun he 0))

/-- Unbounded timestamps are intentionally outside the injectivity theorem. -/
example : ptr (some (.inr 9)) = ptr (some (.inr 0)) := by decide

#print axioms ParameterizedRules.eval_membership
#print axioms NodeSupport.snapshot_record_support
#print axioms NodeCodes.code_injective
#print axioms FactSupport.closure_valid
#print axioms FactCodes.code_injective
#print axioms TraceCodes.code_injective_on_closure
#print axioms TraceCodes.mem_encoded_iff

end FiniteFactCodesTest
