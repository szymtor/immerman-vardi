import Lax751879Proofs.PushPatterns

namespace Lax751879Proofs.PushRules

open Turing Lax751879.OrderedStructures
open RuleConstants ControlRules

variable {σ : Vocabulary} {tm : FinTM2} {m d w : Nat}

noncomputable def transition (tm : FinTM2) (m d w : Nat)
    (c : TM2Micro.Cursor tm.Γ tm.Λ tm.σ) (v : tm.σ) (e : PushEffects.Effect tm) (emit : Bool) :
    Template σ m (FactCodes.payloadWidth tm d w + 1) (MachineConstants.bound tm) where
  numVars := numVars tm m d w
  guard := AddressFormulas.successor (before m d (headWidth tm w)) (after m d (headWidth tm w))
  guard_firstOrder := AddressFormulas.successor_firstOrder _ _
  parameters := query m d (headWidth tm w)
  head := PushPatterns.pattern tm m d w e v emit
  premises := [ControlRules.pattern tm m d w c v (before m d (headWidth tm w))]

theorem transition_holds (c : TM2Micro.Cursor tm.Γ tm.Λ tm.σ) (v : tm.σ)
    (e : PushEffects.Effect tm) (emit : Bool)
    (A : OrderedStructure σ) (hn : MachineConstants.bound tm ≤ A.size)
    (q : Fin m → Fin A.size) (R : Set (Fin (FactCodes.payloadWidth tm d w + 1) → Fin A.size))
    (out : Fin (FactCodes.payloadWidth tm d w + 1) → Fin A.size) :
    (compile (transition tm m d w c v e emit)).holds A q R out ↔
      ∃ x y : Fin d → Fin A.size, ∃ h : Fin (headWidth tm w) → Fin A.size,
        (TupleAddresses.address A.size d x).val + 1 = (TupleAddresses.address A.size d y).val ∧
        PushPatterns.value hn e v emit x y h = out ∧ ControlRules.value hn c v x h ∈ R := by
  rw [compile_holds _ A hn]
  dsimp only [holds, transition]
  constructor
  · rintro ⟨a, hg, _, he, hp⟩
    refine ⟨a ∘ before m d (headWidth tm w), a ∘ after m d (headWidth tm w),
      a ∘ ControlRules.heads m d (headWidth tm w), ?_, ?_, ?_⟩
    · exact (AddressFormulas.eval_successor _ _ _ _ _).mp hg
    · exact (PushPatterns.assignment_pattern hn a e v emit).symm.trans he
    · have hh := hp _ (List.mem_singleton_self _)
      rw [ControlRules.assignment_pattern hn a c v (before m d (headWidth tm w))] at hh
      exact hh
  · rintro ⟨x, y, h, hs, he, hp⟩
    refine ⟨data q x y h, ?_, data_query q x y h, ?_, ?_⟩
    · apply (AddressFormulas.eval_successor _ _ _ _ _).mpr
      simpa only [data_before q x y h, data_after q x y h] using hs
    · rw [PushPatterns.assignment_pattern hn (data q x y h) e v emit,
        data_before q x y h, data_after q x y h, data_heads q x y h]
      exact he
    · intro b hb
      have hb' : b = ControlRules.pattern tm m d w c v (before m d (headWidth tm w)) := List.mem_singleton.mp hb
      subst b
      rw [ControlRules.assignment_pattern hn (data q x y h) c v (before m d (headWidth tm w)),
        data_before q x y h, data_heads q x y h]
      exact hp

open scoped Classical in
noncomputable def rules (tm : FinTM2) (σ : Vocabulary) (m d w : Nat) (emit : Bool) :
    List (ParameterizedRules.Rule σ m (FactCodes.payloadWidth tm d w + 1)) :=
  letI := tm.σFin
  (Finset.univ : Finset (TM2MicroSupport.Control tm × tm.σ)).toList.flatMap fun cv =>
    (PushEffects.target tm cv.1.val cv.2).toList.map fun e =>
      compile (transition tm m d w cv.1.val cv.2 e emit)

theorem mem_rules (tm : FinTM2) (σ : Vocabulary) (m d w : Nat) (emit : Bool)
    (r : ParameterizedRules.Rule σ m (FactCodes.payloadWidth tm d w + 1)) :
    r ∈ rules tm σ m d w emit ↔
      ∃ c ∈ TM2MicroSupport.controls tm, ∃ v e, PushEffects.target tm c v = some e ∧
        compile (transition tm m d w c v e emit) = r := by
  classical
  letI := tm.σFin
  simp only [rules, List.mem_flatMap, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and,
    Option.mem_toList]
  constructor
  · rintro ⟨⟨c, v⟩, e, ht, hr⟩
    exact ⟨c.val, c.property, v, e, ht, hr⟩
  · rintro ⟨c, hc, v, e, ht, hr⟩
    exact ⟨(⟨c, hc⟩, v), e, ht, hr⟩

theorem operator_iff (tm : FinTM2) {σ : Vocabulary} {m d w : Nat} (emit : Bool)
    (A : OrderedStructure σ) (hn : MachineConstants.bound tm ≤ A.size)
    (q : Fin m → Fin A.size)
    (R : Set (Fin (FactCodes.payloadWidth tm d w + 1) → Fin A.size))
    (out : Fin (FactCodes.payloadWidth tm d w + 1) → Fin A.size) :
    out ∈ ParameterizedRules.operator (rules tm σ m d w emit) A q R ↔
      ∃ c ∈ TM2MicroSupport.controls tm, ∃ v e, PushEffects.target tm c v = some e ∧
        ∃ x y : Fin d → Fin A.size, ∃ h : Fin (headWidth tm w) → Fin A.size,
          (TupleAddresses.address A.size d x).val + 1 = (TupleAddresses.address A.size d y).val ∧
          PushPatterns.value hn e v emit x y h = out ∧ ControlRules.value hn c v x h ∈ R := by
  constructor
  · rintro ⟨r, hr, ho⟩
    obtain ⟨c, hc, v, e, ht, rfl⟩ := (mem_rules tm σ m d w emit r).mp hr
    exact ⟨c, hc, v, e, ht, (transition_holds c v e emit A hn q R out).mp ho⟩
  · rintro ⟨c, hc, v, e, ht, ho⟩
    refine ⟨_, (mem_rules tm σ m d w emit _).mpr ⟨c, hc, v, e, ht, rfl⟩, ?_⟩
    exact (transition_holds c v e emit A hn q R out).mpr ho

end Lax751879Proofs.PushRules
