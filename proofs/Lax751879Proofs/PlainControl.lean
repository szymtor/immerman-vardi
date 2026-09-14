import Lax751879Proofs.ControlRules

namespace Lax751879Proofs.PlainControl

open Turing Lax751879.OrderedStructures

/-- The stack-preserving instruction cases. Stack operations are supplied
by separate rules that inspect or create node records. -/
def target (tm : FinTM2) (c : TM2Micro.Cursor tm.Γ tm.Λ tm.σ) (v : tm.σ) :
    Option (TM2Micro.Cursor tm.Γ tm.Λ tm.σ × tm.σ) :=
  match c with
  | .boundary none => some (.boundary none, v)
  | .boundary (some l) => some (.instruction (tm.m l), v)
  | .instruction (.load f q) => some (.instruction q, f v)
  | .instruction (.branch f p q) => some (.instruction (if f v then p else q), v)
  | .instruction (.goto f) => some (.boundary (some (f v)), v)
  | .instruction .halt => some (.boundary none, v)
  | .instruction (.push ..) | .instruction (.pop ..) | .instruction (.peek ..) => none

theorem target_step (tm : FinTM2) {Node : Type} (fresh : Node)
    (H : NodeMachine.Records Node tm.Γ) (heads : tm.K → Option Node)
    {c c' : TM2Micro.Cursor tm.Γ tm.Λ tm.σ} {v v' : tm.σ}
    (ht : target tm c v = some (c', v')) :
    NodeMachine.Step tm.m fresh H ⟨c, v, heads⟩ H ⟨c', v', heads⟩ := by
  cases c with
  | boundary l =>
      cases l with
      | none => cases ht; exact .stopped H v heads
      | some l => cases ht; exact .enter H l v heads
  | instruction q =>
      cases q with
      | push | pop | peek => cases ht
      | load f q => cases ht; exact .load H f q v heads
      | branch f p q => cases ht; exact .branch H f p q v heads
      | goto f => cases ht; exact .goto H f v heads
      | halt => cases ht; exact .halt H v heads

open scoped Classical in
noncomputable def rules (tm : FinTM2) (σ : Vocabulary) (m d w : Nat) :
    List (ParameterizedRules.Rule σ m (FactCodes.payloadWidth tm d w + 1)) :=
  letI := tm.σFin
  (Finset.univ : Finset (TM2MicroSupport.Control tm × tm.σ)).toList.flatMap fun cv =>
    (target tm cv.1.val cv.2).toList.map fun next =>
      RuleConstants.compile (ControlRules.transition tm m d w cv.1.val next.1 cv.2 next.2)

theorem mem_rules (tm : FinTM2) (σ : Vocabulary) (m d w : Nat)
    (r : ParameterizedRules.Rule σ m (FactCodes.payloadWidth tm d w + 1)) :
    r ∈ rules tm σ m d w ↔
      ∃ c ∈ TM2MicroSupport.controls tm, ∃ v c' v', target tm c v = some (c', v') ∧
        RuleConstants.compile (ControlRules.transition tm m d w c c' v v') = r := by
  classical
  letI := tm.σFin
  simp only [rules, List.mem_flatMap, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and,
    Option.mem_toList]
  constructor
  · rintro ⟨⟨c, v⟩, ⟨c', v'⟩, ht, hr⟩
    exact ⟨c.val, c.property, v, c', v', ht, hr⟩
  · rintro ⟨c, hc, v, c', v', ht, hr⟩
    exact ⟨(⟨c, hc⟩, v), (c', v'), ht, hr⟩

theorem operator_iff (tm : FinTM2) {σ : Vocabulary} {m d w : Nat}
    (A : OrderedStructure σ) (hn : MachineConstants.bound tm ≤ A.size)
    (q : Fin m → Fin A.size)
    (R : Set (Fin (FactCodes.payloadWidth tm d w + 1) → Fin A.size))
    (out : Fin (FactCodes.payloadWidth tm d w + 1) → Fin A.size) :
    out ∈ ParameterizedRules.operator (rules tm σ m d w) A q R ↔
      ∃ c ∈ TM2MicroSupport.controls tm, ∃ v c' v', target tm c v = some (c', v') ∧
        ∃ x y : Fin d → Fin A.size, ∃ h : Fin (ControlRules.headWidth tm w) → Fin A.size,
          (TupleAddresses.address A.size d x).val + 1 = (TupleAddresses.address A.size d y).val ∧
          ControlRules.value hn c' v' y h = out ∧ ControlRules.value hn c v x h ∈ R := by
  constructor
  · rintro ⟨r, hr, ho⟩
    obtain ⟨c, hc, v, c', v', ht, rfl⟩ := (mem_rules tm σ m d w r).mp hr
    exact ⟨c, hc, v, c', v', ht, (ControlRules.transition_holds c c' v v' A hn q R out).mp ho⟩
  · rintro ⟨c, hc, v, c', v', ht, ho⟩
    refine ⟨_, (mem_rules tm σ m d w _).mpr ⟨c, hc, v, c', v', ht, rfl⟩, ?_⟩
    exact (ControlRules.transition_holds c c' v v' A hn q R out).mpr ho

end Lax751879Proofs.PlainControl
