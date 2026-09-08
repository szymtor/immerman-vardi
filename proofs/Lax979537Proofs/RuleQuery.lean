import Lax979537Proofs.ParameterizedRules

namespace Lax979537Proofs.RuleQuery

open Lax979537.OrderedStructures Lax979537.FixedPointSyntax Lax979537.FixedPointSemantics
open ParameterizedRules FormulaMacros TupleOrder SyntaxOperations

/-- Existentially test a rule's guard and premises against the LFP of a
fixed rule list. The head is not needed as an extra free argument. -/
def formula {σ : Vocabulary} {m k : Nat} (r : Rule σ m k) (rs : List (Rule σ m k)) : RawFormula σ m [] :=
  existsBlock r.numVars
    (.conj (rename r.guard (Fin.castAdd m))
      (.conj (allOf ((List.finRange m).map fun i =>
        .equal (Fin.castAdd m (r.parameters i)) (Fin.natAdd r.numVars i)))
        (allOf (r.premises.map fun b => membership rs (Fin.castAdd m ∘ r.parameters) (Fin.castAdd m ∘ b)))))

theorem admissible {σ : Vocabulary} {m k : Nat} (r : Rule σ m k) (rs : List (Rule σ m k)) :
    (formula r rs).Admissible := by
  apply (existsBlock_admissible _ _).mpr
  refine ⟨(rename_admissible _ _).mpr (firstOrder_admissible _ r.guard_firstOrder), ?_, ?_⟩
  · simp [admissible_allOf, RawFormula.Admissible]
  · simp only [admissible_allOf, List.forall_mem_map]
    exact fun b _ => membership_admissible _ _ _

theorem eval_formula {σ : Vocabulary} {m k : Nat} (r : Rule σ m k) (rs : List (Rule σ m k))
    (A : OrderedStructure σ) (q : Fin m → Fin A.size) :
    eval (formula r rs) A q (fun i => Fin.elim0 i) ↔
      ∃ out, r.holds A q (Lax979537.LeastFixedPoints.leastFixedPoint (operator rs A q)) out := by
  rw [formula, eval_existsBlock]
  have hv (v : Fin r.numVars → Fin A.size) : Fin.append v q ∘ Fin.castAdd m = v := by
    funext i; simp
  simp only [eval, eval_rename, eval_allOf, List.forall_mem_map, List.mem_finRange, forall_const,
    Fin.append_left, Fin.append_right, eval_membership, ← Function.comp_assoc, hv]
  constructor
  · rintro ⟨v, hg, hq, hp⟩
    have he : v ∘ r.parameters = q := funext hq
    rw [he] at hp
    exact ⟨v ∘ r.head, v, hg, he, rfl, hp⟩
  · rintro ⟨out, v, hg, hq, _, hp⟩
    refine ⟨v, hg, fun i => congrFun hq i, ?_⟩
    rwa [hq]

end Lax979537Proofs.RuleQuery
