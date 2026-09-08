import Lax979537Proofs.PushClosure
import Lax979537Proofs.EmptyReadClosure
import Lax979537Proofs.NonemptyReadClosure

namespace Lax979537Proofs.TransitionRules

open Turing Lax979537.OrderedStructures

/-- All machine transitions, including the separate push-record conclusion.
Initialization is supplied by a separate finite rule family. -/
noncomputable def rules (tm : FinTM2) (σ : Vocabulary) (m d w : Nat) :
    List (ParameterizedRules.Rule σ m (FactCodes.payloadWidth tm d w + 1)) :=
  PlainControl.rules tm σ m d w ++ (PushRules.rules tm σ m d w false ++
    (PushRules.rules tm σ m d w true ++ (EmptyReadRules.rules tm σ m d w ++
      NonemptyReadRules.rules tm σ m d w)))

theorem operator_iff (tm : FinTM2) {σ : Vocabulary} {m d w : Nat}
    (A : OrderedStructure σ) (q : Fin m → Fin A.size)
    (R : Set (Fin (FactCodes.payloadWidth tm d w + 1) → Fin A.size))
    (out : Fin (FactCodes.payloadWidth tm d w + 1) → Fin A.size) :
    out ∈ ParameterizedRules.operator (rules tm σ m d w) A q R ↔
      out ∈ ParameterizedRules.operator (PlainControl.rules tm σ m d w) A q R ∨
      out ∈ ParameterizedRules.operator (PushRules.rules tm σ m d w false) A q R ∨
      out ∈ ParameterizedRules.operator (PushRules.rules tm σ m d w true) A q R ∨
      out ∈ ParameterizedRules.operator (EmptyReadRules.rules tm σ m d w) A q R ∨
      out ∈ ParameterizedRules.operator (NonemptyReadRules.rules tm σ m d w) A q R := by
  simp only [ParameterizedRules.operator, rules, Set.mem_setOf_eq, List.mem_append, or_and_right, exists_or]

theorem plain (tm : FinTM2) {σ : Vocabulary} {m d w : Nat}
    (A : OrderedStructure σ) (q : Fin m → Fin A.size) (R) :
    ParameterizedRules.operator (PlainControl.rules tm σ m d w) A q R ⊆
      ParameterizedRules.operator (rules tm σ m d w) A q R :=
  fun out ho => (operator_iff tm A q R out).mpr (Or.inl ho)

theorem push (tm : FinTM2) {σ : Vocabulary} {m d w : Nat} (emit : Bool)
    (A : OrderedStructure σ) (q : Fin m → Fin A.size) (R) :
    ParameterizedRules.operator (PushRules.rules tm σ m d w emit) A q R ⊆
      ParameterizedRules.operator (rules tm σ m d w) A q R := by
  intro out ho
  apply (operator_iff tm A q R out).mpr
  cases emit with
  | false => exact Or.inr (Or.inl ho)
  | true => exact Or.inr (Or.inr (Or.inl ho))

theorem empty (tm : FinTM2) {σ : Vocabulary} {m d w : Nat}
    (A : OrderedStructure σ) (q : Fin m → Fin A.size) (R) :
    ParameterizedRules.operator (EmptyReadRules.rules tm σ m d w) A q R ⊆
      ParameterizedRules.operator (rules tm σ m d w) A q R :=
  fun out ho => (operator_iff tm A q R out).mpr (Or.inr (Or.inr (Or.inr (Or.inl ho))))

theorem nonempty (tm : FinTM2) {σ : Vocabulary} {m d w : Nat}
    (A : OrderedStructure σ) (q : Fin m → Fin A.size) (R) :
    ParameterizedRules.operator (NonemptyReadRules.rules tm σ m d w) A q R ⊆
      ParameterizedRules.operator (rules tm σ m d w) A q R :=
  fun out ho => (operator_iff tm A q R out).mpr (Or.inr (Or.inr (Or.inr (Or.inr ho))))

theorem preserves {f : List Bool → Bool} (h : TM2ComputableInPolyTime id (fun b : Bool => [b]) f)
    {σ : Vocabulary} {m : Nat} (d : Nat) (A : PointedStructure σ m)
    (hn : TraceCodes.threshold h.tm σ m ≤ A.structureValue.size) :
    ParameterizedRules.operator (rules h.tm σ m d (TraceCodes.nodeWidth σ d))
      A.structureValue A.tuple (TraceCodes.encoded h d A hn) ⊆ TraceCodes.encoded h d A hn := by
  intro out ho
  rcases (operator_iff h.tm A.structureValue A.tuple _ out).mp ho with ho | ho | ho | ho | ho
  · exact PlainClosure.preserves h d A hn ho
  · exact PushClosure.preserves h d A hn false ho
  · exact PushClosure.preserves h d A hn true ho
  · exact EmptyReadClosure.preserves h d A hn ho
  · exact NonemptyReadClosure.preserves h d A hn ho

end Lax979537Proofs.TransitionRules
