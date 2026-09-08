import Lax979537Proofs.InitialConfigRules
import Lax979537Proofs.PlainClosure

namespace Lax979537Proofs.InitialConfigSemantics

open Turing Lax979537.OrderedStructures Lax979537.FixedPointSemantics
open InitialConfigRules RuleConstants InputSegments

theorem first_exists {σ : Vocabulary} {m : Nat} (A : PointedStructure σ m)
    (hi : InputTupleCodes.tagBound σ m ≤ A.structureValue.size) :
    ∃ p, SortedLinks.First (positions A) (InputOrder.rank A hi InputTupleCodes.arity_le_width) p := by
  have hp : (⟨.headerEnd, Fin.elim0⟩ : Identifier σ m A.structureValue.size) ∈ positions A :=
    (mem_positions A _).mpr (by simp [locals])
  let i : Fin (positions A).length := ⟨0, List.length_pos_of_mem hp⟩
  exact ⟨(positions A).get i,
    (SortedLinks.first_iff _ _ (InputOrder.rank_sorted A hi InputTupleCodes.arity_le_width) _).mpr ⟨i, rfl, rfl⟩⟩

variable (tm : FinTM2) (e : tm.Γ tm.k₀ ≃ Bool) {σ : Vocabulary} {m : Nat}
    (d : Nat) (A : PointedStructure σ m) (hn : TraceCodes.threshold tm σ m ≤ A.structureValue.size)

theorem config_of_first (hi : InputTupleCodes.tagBound σ m ≤ A.structureValue.size)
    (p : Identifier σ m A.structureValue.size)
    (hp : SortedLinks.First (positions A) (InputOrder.rank A hi InputTupleCodes.arity_le_width) p) :
    NodeInput.config tm (InitialInput.raw tm e A) (InitialInput.names tm e A) = initial tm p := by
  have hh := (InitialInput.head_iff tm e A hi InputTupleCodes.arity_le_width p).mpr hp
  unfold NodeInput.config initial
  rw [hh]

theorem holds
    (R : Set (Fin (TraceCodes.arity tm σ d) → Fin A.structureValue.size))
    (out : Fin (TraceCodes.arity tm σ d) → Fin A.structureValue.size) :
    (compile (rule tm σ m d (TraceCodes.nodeWidth σ d))).holds A.structureValue A.tuple R out ↔
      TraceCodes.code tm d A hn (.config 0 (NodeInput.config tm (InitialInput.raw tm e A) (InitialInput.names tm e A))) = out := by
  have hm := (PlainClosure.machine_bound tm σ m).trans hn
  have hi : InputTupleCodes.tagBound σ m ≤ A.structureValue.size := by unfold TraceCodes.threshold at hn; omega
  have hnpos : 0 < A.structureValue.size := by unfold TraceCodes.threshold at hn; omega
  rw [compile_holds _ _ hm]
  dsimp only [RuleConstants.holds, rule]
  constructor
  · rintro ⟨v, ⟨ht, hp⟩, hq, he, _⟩
    have ht' := (AddressFormulas.eval_first (ρ := []) (time σ m d) A.structureValue v (fun i => Fin.elim0 i)).mp ht
    have hp' := (InputLinkFormulas.eval_first (ρ := []) InputTupleCodes.arity_le_width (query σ m d) (position σ m d)
      A.structureValue hi v (fun i => Fin.elim0 i)).mp hp
    rw [hq] at hp'
    obtain ⟨p, hcode, hp⟩ := hp'
    have hx : v ∘ time σ m d = TupleCoding.clock hnpos 0 := by
      rw [← ht']
      exact (ControlValues.clock_of_address hnpos _).symm
    have hv : value (w := TraceCodes.nodeWidth σ d) hm (v ∘ time σ m d) (v ∘ position σ m d) =
        TraceCodes.code tm d A hn (.config 0 (initial tm p)) := by
      rw [hx, ← hcode]
      exact value_code (TraceCodes.parameters tm d A hn) hm 0 p
    rw [config_of_first tm e A hi p hp]
    exact hv.symm.trans ((assignment_pattern hm v).symm.trans he)
  · intro he
    obtain ⟨p, hp⟩ := first_exists A hi
    let x := TupleCoding.clock (d := d) hnpos 0
    let y := InputTupleCodes.code hi InputTupleCodes.arity_le_width p
    refine ⟨data A.tuple x y, ⟨?_, ?_⟩, data_query A.tuple x y, ?_, ?_⟩
    · apply (AddressFormulas.eval_first (ρ := []) (time σ m d) A.structureValue _ (fun i => Fin.elim0 i)).mpr
      rw [data_time]
      simp [x, TupleCoding.clock_address]
    · apply (InputLinkFormulas.eval_first (ρ := []) InputTupleCodes.arity_le_width (query σ m d) (position σ m d)
        A.structureValue hi _ (fun i => Fin.elim0 i)).mpr
      rw [data_query, data_position]
      exact ⟨p, rfl, hp⟩
    · rw [assignment_pattern hm _, data_time, data_position]
      rw [config_of_first tm e A hi p hp] at he
      exact (value_code (TraceCodes.parameters tm d A hn) hm 0 p).trans he
    · intro r hr; cases hr

end Lax979537Proofs.InitialConfigSemantics
