import Lax979537Proofs.NonemptyPatterns
import Lax979537Proofs.ReadSymbols

namespace Lax979537Proofs.NonemptyReadRules

open Turing Lax979537.OrderedStructures RuleConstants NonemptyPatterns

variable {σ : Vocabulary} {tm : FinTM2} {m d w : Nat}

noncomputable def transition (tm : FinTM2) (m d w : Nat)
    (c : TM2Micro.Cursor tm.Γ tm.Λ tm.σ) (v : tm.σ) (e : ReadEffects.Effect tm) (a : tm.Γ e.key) :
    Template σ m (FactCodes.payloadWidth tm d w + 1) (MachineConstants.bound tm) where
  numVars := numVars tm m d w
  guard := AddressFormulas.successor (xvars tm m d w) (yvars tm m d w)
  guard_firstOrder := AddressFormulas.successor_firstOrder _ _
  parameters := qvars tm m d w
  head := output tm m d w e a
  premises := [source tm m d w c v, node tm m d w e a]

theorem transition_holds (c : TM2Micro.Cursor tm.Γ tm.Λ tm.σ) (v : tm.σ)
    (e : ReadEffects.Effect tm) (a : tm.Γ e.key)
    (A : OrderedStructure σ) (hn : MachineConstants.bound tm ≤ A.size)
    (q : Fin m → Fin A.size) (R : Set (Fin (FactCodes.payloadWidth tm d w + 1) → Fin A.size))
    (out : Fin (FactCodes.payloadWidth tm d w + 1) → Fin A.size) :
    (compile (transition tm m d w c v e a)).holds A q R out ↔
      ∃ x y : Fin d → Fin A.size, ∃ h : Fin (ControlRules.headWidth tm w) → Fin A.size,
        ∃ p : Fin (w + 1) → Fin A.size,
          (TupleAddresses.address A.size d x).val + 1 = (TupleAddresses.address A.size d y).val ∧
          ReadPatterns.value hn e a y h p = out ∧ ControlRules.value hn c v x h ∈ R ∧
          ReadPatterns.nodeValue (d := d) hn (Sigma.mk e.key a) (HeadPatterns.get tm h e.key) p ∈ R := by
  rw [compile_holds _ A hn]
  dsimp only [holds, transition]
  constructor
  · rintro ⟨v, hg, _, he, hp⟩
    refine ⟨v ∘ xvars tm m d w, v ∘ yvars tm m d w, v ∘ hvars tm m d w, v ∘ pvars tm m d w,
      (AddressFormulas.eval_successor _ _ _ _ _).mp hg, ?_, ?_, ?_⟩
    · exact (assignment_output hn v e a).symm.trans he
    · have hh := hp _ (List.mem_cons_self ..)
      rw [assignment_source] at hh
      exact hh
    · have hh := hp _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
      rw [assignment_node] at hh
      exact hh
  · rintro ⟨x, y, h, p, hs, he, hc, hp⟩
    refine ⟨data q x y h p, ?_, data_q q x y h p, ?_, ?_⟩
    · apply (AddressFormulas.eval_successor _ _ _ _ _).mpr
      simpa only [data_x q x y h p, data_y q x y h p] using hs
    · rw [assignment_output, data_y q x y h p, data_h q x y h p, data_p q x y h p]
      exact he
    · intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · rw [assignment_source, data_x q x y h p, data_h q x y h p]
        exact hc
      · have hb' : b = node tm m d w e a := List.mem_singleton.mp hb
        subst b
        rw [assignment_node, data_h q x y h p, data_p q x y h p]
        exact hp

open scoped Classical in
noncomputable def rules (tm : FinTM2) (σ : Vocabulary) (m d w : Nat) :
    List (ParameterizedRules.Rule σ m (FactCodes.payloadWidth tm d w + 1)) :=
  letI := tm.σFin
  (Finset.univ : Finset (TM2MicroSupport.Control tm × tm.σ)).toList.flatMap fun cv =>
    (ReadEffects.target tm cv.1.val cv.2).toList.flatMap fun e =>
      (ReadSymbols.values tm e.key).map fun a => compile (transition tm m d w cv.1.val cv.2 e a)

theorem mem_rules (tm : FinTM2) (σ : Vocabulary) (m d w : Nat)
    (r : ParameterizedRules.Rule σ m (FactCodes.payloadWidth tm d w + 1)) :
    r ∈ rules tm σ m d w ↔
      ∃ c ∈ TM2MicroSupport.controls tm, ∃ v e, ReadEffects.target tm c v = some e ∧
        ∃ a : tm.Γ e.key, Sigma.mk e.key a ∈ TM2Alphabet.alphabet tm ∧
          compile (transition tm m d w c v e a) = r := by
  classical
  letI := tm.σFin
  simp only [rules, List.mem_flatMap, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and,
    Option.mem_toList, ReadSymbols.mem_values]
  constructor
  · rintro ⟨⟨c, v⟩, e, ht, a, ha, hr⟩
    exact ⟨c.val, c.property, v, e, ht, a, ha, hr⟩
  · rintro ⟨c, hc, v, e, ht, a, ha, hr⟩
    exact ⟨(⟨c, hc⟩, v), e, ht, a, ha, hr⟩

theorem operator_iff (tm : FinTM2) {σ : Vocabulary} {m d w : Nat}
    (A : OrderedStructure σ) (hn : MachineConstants.bound tm ≤ A.size)
    (q : Fin m → Fin A.size)
    (R : Set (Fin (FactCodes.payloadWidth tm d w + 1) → Fin A.size))
    (out : Fin (FactCodes.payloadWidth tm d w + 1) → Fin A.size) :
    out ∈ ParameterizedRules.operator (rules tm σ m d w) A q R ↔
      ∃ c ∈ TM2MicroSupport.controls tm, ∃ v e, ReadEffects.target tm c v = some e ∧
        ∃ a : tm.Γ e.key, Sigma.mk e.key a ∈ TM2Alphabet.alphabet tm ∧
          ∃ x y : Fin d → Fin A.size, ∃ h : Fin (ControlRules.headWidth tm w) → Fin A.size,
            ∃ p : Fin (w + 1) → Fin A.size,
              (TupleAddresses.address A.size d x).val + 1 = (TupleAddresses.address A.size d y).val ∧
              ReadPatterns.value hn e a y h p = out ∧ ControlRules.value hn c v x h ∈ R ∧
              ReadPatterns.nodeValue (d := d) hn (Sigma.mk e.key a) (HeadPatterns.get tm h e.key) p ∈ R := by
  constructor
  · rintro ⟨r, hr, ho⟩
    obtain ⟨c, hc, v, e, ht, a, ha, rfl⟩ := (mem_rules tm σ m d w r).mp hr
    exact ⟨c, hc, v, e, ht, a, ha, (transition_holds c v e a A hn q R out).mp ho⟩
  · rintro ⟨c, hc, v, e, ht, a, ha, ho⟩
    refine ⟨_, (mem_rules tm σ m d w _).mpr ⟨c, hc, v, e, ht, a, ha, rfl⟩, ?_⟩
    exact (transition_holds c v e a A hn q R out).mpr ho

end Lax979537Proofs.NonemptyReadRules
