import Lax751879Proofs.InitialNodeRules
import Lax751879Proofs.PlainClosure

namespace Lax751879Proofs.InitialNodeSemantics

open Turing Lax751879.OrderedStructures Lax751879.FixedPointSemantics
open InitialNodeRules RuleConstants InputSegments

variable (tm : FinTM2) (e : tm.Γ tm.k₀ ≃ Bool) {σ : Vocabulary} {m : Nat}
    (d : Nat) (A : PointedStructure σ m) (hn : TraceCodes.threshold tm σ m ≤ A.structureValue.size)

theorem holds_last (b : Bool)
    (R : Set (Fin (TraceCodes.arity tm σ d) → Fin A.structureValue.size))
    (out : Fin (TraceCodes.arity tm σ d) → Fin A.structureValue.size) :
    (compile (rule tm e σ m d (TraceCodes.nodeWidth σ d) b true)).holds A.structureValue A.tuple R out ↔
      ∃ p : Identifier σ m A.structureValue.size, bit A p.1 p.2 = b ∧
        SortedLinks.Last (positions A) (InputOrder.rank A (by unfold TraceCodes.threshold at hn; omega)
          InputTupleCodes.arity_le_width) p ∧
        TraceCodes.code tm d A hn (.node (.inl p, Sigma.mk tm.k₀ (e.symm b), none)) = out := by
  have hm := (PlainClosure.machine_bound tm σ m).trans hn
  have hi : InputTupleCodes.tagBound σ m ≤ A.structureValue.size := by unfold TraceCodes.threshold at hn; omega
  rw [compile_holds _ _ hm]
  dsimp only [holds, rule]
  constructor
  · rintro ⟨v, ⟨hb, hl⟩, hq, he, _⟩
    have hb' := (InputBitFormulas.eval_hasBit (ρ := []) InputTupleCodes.arity_le_width (query σ m) (left σ m)
      b A.structureValue hi v (fun i => Fin.elim0 i)).mp hb
    have hl' := (InputLinkFormulas.eval_last (ρ := []) InputTupleCodes.arity_le_width (query σ m) (left σ m)
      A.structureValue hi v (fun i => Fin.elim0 i)).mp hl
    rw [hq] at hb' hl'
    obtain ⟨p, _, hp, hb⟩ := hb'
    obtain ⟨q, hqcode, hl⟩ := hl'
    have hqp := InputTupleCodes.code_injective hi InputTupleCodes.arity_le_width (hqcode.trans hp.symm)
    subst q
    have hv : value (d := d) (w := TraceCodes.nodeWidth σ d) e hm b true
        (v ∘ left σ m) (v ∘ right σ m) =
        TraceCodes.code tm d A hn (.node (.inl p, Sigma.mk tm.k₀ (e.symm b), none)) := by
      rw [← hp]
      exact value_code e (TraceCodes.parameters tm d A hn) hm b true p p
    exact ⟨p, hb, hl, hv.symm.trans ((assignment_pattern e hm v b true).symm.trans he)⟩
  · rintro ⟨p, hb, hl, he⟩
    let x := InputTupleCodes.code hi InputTupleCodes.arity_le_width p
    refine ⟨data A.tuple x x, ⟨?_, ?_⟩, data_query A.tuple x x, ?_, ?_⟩
    · apply (InputBitFormulas.eval_hasBit (ρ := []) InputTupleCodes.arity_le_width (query σ m) (left σ m)
        b A.structureValue hi _ (fun i => Fin.elim0 i)).mpr
      rw [data_query, data_left]
      exact ⟨p, hl.1, rfl, hb⟩
    · apply (InputLinkFormulas.eval_last (ρ := []) InputTupleCodes.arity_le_width (query σ m) (left σ m)
        A.structureValue hi _ (fun i => Fin.elim0 i)).mpr
      rw [data_query, data_left]
      exact ⟨p, rfl, hl⟩
    · rw [assignment_pattern e hm _ b true, data_left, data_right]
      exact (value_code e (TraceCodes.parameters tm d A hn) hm b true p p).trans he
    · intro r hr; cases hr

theorem holds_next (b : Bool)
    (R : Set (Fin (TraceCodes.arity tm σ d) → Fin A.structureValue.size))
    (out : Fin (TraceCodes.arity tm σ d) → Fin A.structureValue.size) :
    (compile (rule tm e σ m d (TraceCodes.nodeWidth σ d) b false)).holds A.structureValue A.tuple R out ↔
      ∃ p q : Identifier σ m A.structureValue.size, bit A p.1 p.2 = b ∧
        SortedLinks.Next (positions A) (InputOrder.rank A (by unfold TraceCodes.threshold at hn; omega)
          InputTupleCodes.arity_le_width) p q ∧
        TraceCodes.code tm d A hn (.node (.inl p, Sigma.mk tm.k₀ (e.symm b), some (.inl q))) = out := by
  have hm := (PlainClosure.machine_bound tm σ m).trans hn
  have hi : InputTupleCodes.tagBound σ m ≤ A.structureValue.size := by unfold TraceCodes.threshold at hn; omega
  rw [compile_holds _ _ hm]
  dsimp only [holds, rule]
  constructor
  · rintro ⟨v, ⟨hb, hl⟩, hq, he, _⟩
    have hb' := (InputBitFormulas.eval_hasBit (ρ := []) InputTupleCodes.arity_le_width (query σ m) (left σ m)
      b A.structureValue hi v (fun i => Fin.elim0 i)).mp hb
    have hl' := (InputLinkFormulas.eval_next (ρ := []) InputTupleCodes.arity_le_width (query σ m) (left σ m) (right σ m)
      A.structureValue hi v (fun i => Fin.elim0 i)).mp hl
    rw [hq] at hb' hl'
    obtain ⟨p, _, hp, hb⟩ := hb'
    obtain ⟨p', q, hp', hqcode, hl⟩ := hl'
    have hpp := InputTupleCodes.code_injective hi InputTupleCodes.arity_le_width (hp'.trans hp.symm)
    subst p'
    have hv : value (d := d) (w := TraceCodes.nodeWidth σ d) e hm b false
        (v ∘ left σ m) (v ∘ right σ m) =
        TraceCodes.code tm d A hn (.node (.inl p, Sigma.mk tm.k₀ (e.symm b), some (.inl q))) := by
      rw [← hp, ← hqcode]
      exact value_code e (TraceCodes.parameters tm d A hn) hm b false p q
    exact ⟨p, q, hb, hl, hv.symm.trans ((assignment_pattern e hm v b false).symm.trans he)⟩
  · rintro ⟨p, q, hb, hl, he⟩
    let x := InputTupleCodes.code hi InputTupleCodes.arity_le_width p
    let y := InputTupleCodes.code hi InputTupleCodes.arity_le_width q
    refine ⟨data A.tuple x y, ⟨?_, ?_⟩, data_query A.tuple x y, ?_, ?_⟩
    · apply (InputBitFormulas.eval_hasBit (ρ := []) InputTupleCodes.arity_le_width (query σ m) (left σ m)
        b A.structureValue hi _ (fun i => Fin.elim0 i)).mpr
      rw [data_query, data_left]
      exact ⟨p, hl.1, rfl, hb⟩
    · apply (InputLinkFormulas.eval_next (ρ := []) InputTupleCodes.arity_le_width (query σ m) (left σ m) (right σ m)
        A.structureValue hi _ (fun i => Fin.elim0 i)).mpr
      rw [data_query, data_left, data_right]
      exact ⟨p, q, rfl, rfl, hl⟩
    · rw [assignment_pattern e hm _ b false, data_left, data_right]
      exact (value_code e (TraceCodes.parameters tm d A hn) hm b false p q).trans he
    · intro r hr; cases hr

end Lax751879Proofs.InitialNodeSemantics
