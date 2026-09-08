import Lax979537Proofs.EmptyHead
import Lax979537Proofs.ReadEffects

namespace Lax979537Proofs.EmptyReadRules

open Turing Lax979537.OrderedStructures Lax979537.FixedPointSemantics
open RuleConstants ControlRules

variable {σ : Vocabulary} {tm : FinTM2} {m d w : Nat}

noncomputable def transition (tm : FinTM2) (m d w : Nat)
    (c : TM2Micro.Cursor tm.Γ tm.Λ tm.σ) (v : tm.σ) (e : ReadEffects.Effect tm) :
    Template σ m (FactCodes.payloadWidth tm d w + 1) (MachineConstants.bound tm) where
  numVars := numVars tm m d w
  guard := .conj
    (AddressFormulas.successor (before m d (headWidth tm w)) (after m d (headWidth tm w)))
    (EmptyHead.formula (HeadPatterns.get tm (ControlRules.heads m d (headWidth tm w)) e.key))
  guard_firstOrder := ⟨AddressFormulas.successor_firstOrder _ _, EmptyHead.firstOrder _⟩
  parameters := query m d (headWidth tm w)
  head := ControlRules.pattern tm m d w e.next (e.state none) (after m d (headWidth tm w))
  premises := [ControlRules.pattern tm m d w c v (before m d (headWidth tm w))]

theorem transition_holds (c : TM2Micro.Cursor tm.Γ tm.Λ tm.σ) (v : tm.σ) (e : ReadEffects.Effect tm)
    (A : OrderedStructure σ) (hn : MachineConstants.bound tm ≤ A.size)
    (q : Fin m → Fin A.size) (R : Set (Fin (FactCodes.payloadWidth tm d w + 1) → Fin A.size))
    (out : Fin (FactCodes.payloadWidth tm d w + 1) → Fin A.size) :
    (compile (transition tm m d w c v e)).holds A q R out ↔
      ∃ x y : Fin d → Fin A.size, ∃ h : Fin (headWidth tm w) → Fin A.size,
        (TupleAddresses.address A.size d x).val + 1 = (TupleAddresses.address A.size d y).val ∧
        HeadPatterns.get tm h e.key = (fun _ => (⟨0, by have := MachineConstants.enough tm; omega⟩ : Fin A.size)) ∧
        ControlRules.value hn e.next (e.state none) y h = out ∧ ControlRules.value hn c v x h ∈ R := by
  have hnpos : 0 < A.size := by have := MachineConstants.enough tm; omega
  rw [compile_holds _ A hn]
  dsimp only [holds, transition, eval]
  constructor
  · rintro ⟨a, ⟨hs, hz⟩, _, he, hp⟩
    refine ⟨a ∘ before m d (headWidth tm w), a ∘ after m d (headWidth tm w),
      a ∘ ControlRules.heads m d (headWidth tm w), ?_, ?_, ?_, ?_⟩
    · exact (AddressFormulas.eval_successor _ _ _ _ _).mp hs
    · exact (EmptyHead.eval_formula _ A hnpos a).mp hz
    · exact (ControlRules.assignment_pattern hn a e.next (e.state none) _).symm.trans he
    · have hh := hp _ (List.mem_singleton_self _)
      rw [ControlRules.assignment_pattern hn a c v (before m d (headWidth tm w))] at hh
      exact hh
  · rintro ⟨x, y, h, hs, hz, he, hp⟩
    refine ⟨data q x y h, ⟨?_, ?_⟩, data_query q x y h, ?_, ?_⟩
    · apply (AddressFormulas.eval_successor _ _ _ _ _).mpr
      simpa only [data_before q x y h, data_after q x y h] using hs
    · apply (EmptyHead.eval_formula _ A hnpos (data q x y h)).mpr
      rw [HeadPatterns.map_get, data_heads q x y h]
      exact hz
    · rw [ControlRules.assignment_pattern hn (data q x y h) e.next (e.state none) _,
        data_after q x y h, data_heads q x y h]
      exact he
    · intro b hb
      have hb' : b = ControlRules.pattern tm m d w c v (before m d (headWidth tm w)) := List.mem_singleton.mp hb
      subst b
      rw [ControlRules.assignment_pattern hn (data q x y h) c v (before m d (headWidth tm w)),
        data_before q x y h, data_heads q x y h]
      exact hp

open scoped Classical in
noncomputable def rules (tm : FinTM2) (σ : Vocabulary) (m d w : Nat) :
    List (ParameterizedRules.Rule σ m (FactCodes.payloadWidth tm d w + 1)) :=
  letI := tm.σFin
  (Finset.univ : Finset (TM2MicroSupport.Control tm × tm.σ)).toList.flatMap fun cv =>
    (ReadEffects.target tm cv.1.val cv.2).toList.map fun e =>
      compile (transition tm m d w cv.1.val cv.2 e)

theorem mem_rules (tm : FinTM2) (σ : Vocabulary) (m d w : Nat)
    (r : ParameterizedRules.Rule σ m (FactCodes.payloadWidth tm d w + 1)) :
    r ∈ rules tm σ m d w ↔
      ∃ c ∈ TM2MicroSupport.controls tm, ∃ v e, ReadEffects.target tm c v = some e ∧
        compile (transition tm m d w c v e) = r := by
  classical
  letI := tm.σFin
  simp only [rules, List.mem_flatMap, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and,
    Option.mem_toList]
  constructor
  · rintro ⟨⟨c, v⟩, e, ht, hr⟩
    exact ⟨c.val, c.property, v, e, ht, hr⟩
  · rintro ⟨c, hc, v, e, ht, hr⟩
    exact ⟨(⟨c, hc⟩, v), e, ht, hr⟩

theorem operator_iff (tm : FinTM2) {σ : Vocabulary} {m d w : Nat}
    (A : OrderedStructure σ) (hn : MachineConstants.bound tm ≤ A.size)
    (q : Fin m → Fin A.size)
    (R : Set (Fin (FactCodes.payloadWidth tm d w + 1) → Fin A.size))
    (out : Fin (FactCodes.payloadWidth tm d w + 1) → Fin A.size) :
    out ∈ ParameterizedRules.operator (rules tm σ m d w) A q R ↔
      ∃ c ∈ TM2MicroSupport.controls tm, ∃ v e, ReadEffects.target tm c v = some e ∧
        ∃ x y : Fin d → Fin A.size, ∃ h : Fin (headWidth tm w) → Fin A.size,
          (TupleAddresses.address A.size d x).val + 1 = (TupleAddresses.address A.size d y).val ∧
          HeadPatterns.get tm h e.key = (fun _ => (⟨0, by have := MachineConstants.enough tm; omega⟩ : Fin A.size)) ∧
          ControlRules.value hn e.next (e.state none) y h = out ∧ ControlRules.value hn c v x h ∈ R := by
  constructor
  · rintro ⟨r, hr, ho⟩
    obtain ⟨c, hc, v, e, ht, rfl⟩ := (mem_rules tm σ m d w r).mp hr
    exact ⟨c, hc, v, e, ht, (transition_holds c v e A hn q R out).mp ho⟩
  · rintro ⟨c, hc, v, e, ht, ho⟩
    refine ⟨_, (mem_rules tm σ m d w _).mpr ⟨c, hc, v, e, ht, rfl⟩, ?_⟩
    exact (transition_holds c v e A hn q R out).mpr ho

end Lax979537Proofs.EmptyReadRules
