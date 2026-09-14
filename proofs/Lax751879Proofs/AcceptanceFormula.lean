import Lax751879Proofs.AcceptRule
import Lax751879Proofs.RuleQuery
import Lax751879Proofs.CompiledRun

namespace Lax751879Proofs.AcceptanceFormula

open Turing Lax751879.OrderedStructures Lax751879.FixedPointSyntax Lax751879.FixedPointSemantics
open TupleOrder

open scoped Classical in
noncomputable def formula (tm : FinTM2) (input : tm.Γ tm.k₀ ≃ Bool) (answer : tm.Γ tm.k₁)
    (σ : Vocabulary) (m d : Nat) : RawFormula σ m [] :=
  letI := tm.σFin
  anyOf ((Finset.univ : Finset tm.σ).toList.map fun state =>
    RuleQuery.formula (RuleConstants.compile (AcceptRule.template tm answer σ m d (TraceCodes.nodeWidth σ d) state))
      (CompiledRun.rules tm input σ m d))

theorem admissible (tm : FinTM2) (input : tm.Γ tm.k₀ ≃ Bool) (answer : tm.Γ tm.k₁)
    (σ : Vocabulary) (m d : Nat) : (formula tm input answer σ m d).Admissible := by
  classical
  simp only [formula, admissible_anyOf, List.forall_mem_map]
  exact fun _ _ => RuleQuery.admissible _ _

theorem eval_formula {f : List Bool → Bool} (h : TM2ComputableInPolyTime id (fun b : Bool => [b]) f)
    {σ : Vocabulary} {m : Nat} (d : Nat) (A : PointedStructure σ m)
    (hn : TraceCodes.threshold h.tm σ m ≤ A.structureValue.size) (answer : h.tm.Γ h.tm.k₁) :
    eval (formula h.tm h.inputAlphabet answer σ m d) A.structureValue A.tuple (fun i => Fin.elim0 i) ↔
      ∃ state : h.tm.σ, ∃ x : Fin d → Fin A.structureValue.size,
        ∃ heads : Fin (ControlRules.headWidth h.tm (TraceCodes.nodeWidth σ d)) → Fin A.structureValue.size,
          ∃ parent : Fin (TraceCodes.nodeWidth σ d + 1) → Fin A.structureValue.size,
            (TupleAddresses.address A.structureValue.size d x).val + 1 = A.structureValue.size ^ d ∧
            ControlRules.value ((PlainClosure.machine_bound h.tm σ m).trans hn) (.boundary none) state x heads ∈ TraceCodes.encoded h d A hn ∧
            ReadPatterns.nodeValue (d := d) ((PlainClosure.machine_bound h.tm σ m).trans hn) (Sigma.mk h.tm.k₁ answer)
              (HeadPatterns.get h.tm heads h.tm.k₁) parent ∈ TraceCodes.encoded h d A hn := by
  classical
  letI := h.tm.σFin
  simp only [formula, eval_anyOf, exists_map, Finset.mem_toList, Finset.mem_univ, true_and, RuleQuery.eval_formula]
  change (∃ state, ∃ out, (RuleConstants.compile (AcceptRule.template h.tm answer σ m d (TraceCodes.nodeWidth σ d) state)).holds
    A.structureValue A.tuple (CompiledRun.closure h.tm h.inputAlphabet d A) out) ↔ _
  rw [CompiledRun.closure_eq_encoded h d A hn]
  apply exists_congr
  intro state
  exact AcceptRule.holds answer state A.structureValue ((PlainClosure.machine_bound h.tm σ m).trans hn) A.tuple _

end Lax751879Proofs.AcceptanceFormula
