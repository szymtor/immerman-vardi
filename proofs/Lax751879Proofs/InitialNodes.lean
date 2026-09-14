import Lax751879Proofs.InitialNodeSemantics

namespace Lax751879Proofs.InitialNodes

open Turing Lax751879.OrderedStructures RuleConstants InputSegments

noncomputable def rules (tm : FinTM2) (e : tm.Γ tm.k₀ ≃ Bool) (σ : Vocabulary) (m d w : Nat) :
    List (ParameterizedRules.Rule σ m (FactCodes.payloadWidth tm d w + 1)) :=
  [false, true].flatMap fun b => [false, true].map fun terminal =>
    compile (InitialNodeRules.rule tm e σ m d w b terminal)

theorem operator_cases (tm : FinTM2) (e : tm.Γ tm.k₀ ≃ Bool) {σ : Vocabulary} {m d w : Nat}
    (A : OrderedStructure σ) (q : Fin m → Fin A.size) (R)
    (out : Fin (FactCodes.payloadWidth tm d w + 1) → Fin A.size) :
    out ∈ ParameterizedRules.operator (rules tm e σ m d w) A q R ↔
      ∃ b terminal, (compile (InitialNodeRules.rule tm e σ m d w b terminal)).holds A q R out := by
  constructor
  · rintro ⟨r, hr, ho⟩
    obtain ⟨b, _, ht⟩ := List.mem_flatMap.mp hr
    obtain ⟨terminal, _, rfl⟩ := List.mem_map.mp ht
    exact ⟨b, terminal, ho⟩
  · rintro ⟨b, terminal, ho⟩
    refine ⟨_, List.mem_flatMap.mpr ⟨b, ?_, List.mem_map.mpr ⟨terminal, ?_, rfl⟩⟩, ho⟩
    · cases b <;> simp
    · cases terminal <;> simp

theorem operator_iff (tm : FinTM2) (e : tm.Γ tm.k₀ ≃ Bool) {σ : Vocabulary} {m : Nat}
    (d : Nat) (A : PointedStructure σ m) (hn : TraceCodes.threshold tm σ m ≤ A.structureValue.size)
    (R : Set (Fin (TraceCodes.arity tm σ d) → Fin A.structureValue.size))
    (out : Fin (TraceCodes.arity tm σ d) → Fin A.structureValue.size) :
    out ∈ ParameterizedRules.operator (rules tm e σ m d (TraceCodes.nodeWidth σ d)) A.structureValue A.tuple R ↔
      ∃ r ∈ NodeInput.heap tm (InitialInput.raw tm e A) (InitialInput.names tm e A), TraceCodes.code tm d A hn (.node r) = out := by
  have hi : InputTupleCodes.tagBound σ m ≤ A.structureValue.size := by unfold TraceCodes.threshold at hn; omega
  rw [operator_cases]
  constructor
  · rintro ⟨b, terminal, ho⟩
    cases terminal with
    | false =>
        obtain ⟨p, q, hb, hl, he⟩ := (InitialNodeSemantics.holds_next tm e d A hn b R out).mp ho
        refine ⟨(.inl p, Sigma.mk tm.k₀ (e.symm b), some (.inl q)), ?_, he⟩
        apply (InitialInput.heap_iff tm e A hi InputTupleCodes.arity_le_width _ _ _).mpr
        refine ⟨p, some q, rfl, rfl, hl.1, ?_, hl⟩
        rw [hb]
    | true =>
        obtain ⟨p, hb, hl, he⟩ := (InitialNodeSemantics.holds_last tm e d A hn b R out).mp ho
        refine ⟨(.inl p, Sigma.mk tm.k₀ (e.symm b), none), ?_, he⟩
        apply (InitialInput.heap_iff tm e A hi InputTupleCodes.arity_le_width _ _ _).mpr
        refine ⟨p, none, rfl, rfl, hl.1, ?_, hl⟩
        rw [hb]
  · rintro ⟨⟨key, symbol, parent⟩, hr, he⟩
    obtain ⟨p, parent₀, rfl, rfl, _, rfl, hl⟩ :=
      (InitialInput.heap_iff tm e A hi InputTupleCodes.arity_le_width key symbol parent).mp hr
    cases parent₀ with
    | none =>
        refine ⟨bit A p.1 p.2, true, ?_⟩
        exact (InitialNodeSemantics.holds_last tm e d A hn _ R out).mpr ⟨p, rfl, hl, he⟩
    | some q =>
        refine ⟨bit A p.1 p.2, false, ?_⟩
        exact (InitialNodeSemantics.holds_next tm e d A hn _ R out).mpr ⟨p, q, rfl, hl, he⟩

end Lax751879Proofs.InitialNodes
