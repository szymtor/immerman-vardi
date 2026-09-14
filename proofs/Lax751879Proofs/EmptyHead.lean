import Lax751879Proofs.HeadPatterns

namespace Lax751879Proofs.EmptyHead

open Lax751879.OrderedStructures Lax751879.FixedPointSyntax Lax751879.FixedPointSemantics
open TupleOrder FormulaMacros

def formula {σ : Vocabulary} {v k : Nat} (head : Fin k → Fin v) : RawFormula σ v [] :=
  allOf ((List.finRange k).map fun j => AddressFormulas.numeral 0 (head j))

theorem firstOrder {σ : Vocabulary} {v k : Nat} (head : Fin k → Fin v) :
    FirstOrder (formula (σ := σ) head) := by
  simp only [formula, firstOrder_allOf, List.forall_mem_map]
  exact fun j _ => AddressFormulas.numeral_firstOrder _ _

theorem eval_formula {σ : Vocabulary} {v k : Nat} (head : Fin k → Fin v)
    (A : OrderedStructure σ) (hn : 0 < A.size) (a : Fin v → Fin A.size) :
    eval (formula head) A a (fun i => Fin.elim0 i) ↔ a ∘ head = fun _ => (⟨0, hn⟩ : Fin A.size) := by
  simp only [formula, eval_allOf, List.forall_mem_map, List.mem_finRange, forall_const,
    AddressFormulas.eval_numeral]
  constructor
  · intro h; funext j; exact Fin.ext (h j)
  · intro h j; exact congrArg (fun z : Fin A.size => z.val) (congrFun h j)

theorem code_none {Initial : Type} {n iWidth d w : Nat} (hn : 3 ≤ n)
    (initial : Initial → Fin iWidth → Fin n) :
    NodeCodes.code (d := d) (w := w) hn initial none = fun _ => (⟨0, by omega⟩ : Fin n) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

end Lax751879Proofs.EmptyHead
