import Lax979537Proofs.ReadDerivation

namespace Lax979537Proofs.TransitionDerivation

open Turing Lax979537.OrderedStructures

variable {f : List Bool → Bool} (h : TM2ComputableInPolyTime id (fun b : Bool => [b]) f)
    {σ : Vocabulary} {m : Nat} (d : Nat) (A : PointedStructure σ m)
    (hn : TraceCodes.threshold h.tm σ m ≤ A.structureValue.size)

/-- The finite concrete rule list derives every bounded machine step,
including both empty and nonempty read cases. -/
theorem step {t : Nat}
    {H G : NodeMachine.Records (TimedNodes.Node (InputSegments.Identifier σ m A.structureValue.size)) h.tm.Γ}
    {cfg next : NodeMachine.Cfg h.tm.Γ h.tm.Λ h.tm.σ
      (TimedNodes.Node (InputSegments.Identifier σ m A.structureValue.size))}
    (hs : NodeMachine.Step h.tm.m (.inr t) H cfg G next)
    (hc : cfg.cursor ∈ TM2MicroSupport.controls h.tm)
    (ht : t + 1 < A.structureValue.size ^ d)
    (R : Set (Fin (TraceCodes.arity h.tm σ d) → Fin A.structureValue.size))
    (hp : TraceCodes.code h.tm d A hn (.config t cfg) ∈ R)
    (hsupport : ∀ r ∈ H, r.2.1 ∈ TM2Alphabet.alphabet h.tm)
    (hrecords : ∀ r ∈ H, TraceCodes.code h.tm d A hn (.node r) ∈ R) :
    TraceCodes.code h.tm d A hn (.config (t + 1) next) ∈
      ParameterizedRules.operator (TransitionRules.rules h.tm σ m d (TraceCodes.nodeWidth σ d))
        A.structureValue A.tuple R := by
  cases hs with
  | stopped v heads =>
      apply TransitionRules.plain h.tm A.structureValue A.tuple R
      exact PlainClosure.derives h d A hn ⟨.boundary none, v, heads⟩ (.boundary none) v rfl hc ht R hp
  | enter l v heads =>
      apply TransitionRules.plain h.tm A.structureValue A.tuple R
      exact PlainClosure.derives h d A hn ⟨.boundary (some l), v, heads⟩ (.instruction (h.tm.m l)) v rfl hc ht R hp
  | push k f q v heads =>
      apply TransitionRules.push h.tm false A.structureValue A.tuple R
      exact PushClosure.derives h d A hn ⟨.instruction (.push k f q), v, heads⟩
        ⟨k, f v, .instruction q⟩ false rfl hc ht R hp
  | pop k f q v heads a parent hr =>
      exact ReadDerivation.derives h d A hn H ⟨.instruction (.pop k f q), v, heads⟩
        ⟨k, f v, .instruction q, true⟩ a parent rfl hr hc ht R hp hsupport hrecords
  | peek k f q v heads a parent hr =>
      exact ReadDerivation.derives h d A hn H ⟨.instruction (.peek k f q), v, heads⟩
        ⟨k, f v, .instruction q, false⟩ a parent rfl hr hc ht R hp hsupport hrecords
  | load f q v heads =>
      apply TransitionRules.plain h.tm A.structureValue A.tuple R
      exact PlainClosure.derives h d A hn ⟨.instruction (.load f q), v, heads⟩ (.instruction q) (f v) rfl hc ht R hp
  | branch f p q v heads =>
      apply TransitionRules.plain h.tm A.structureValue A.tuple R
      exact PlainClosure.derives h d A hn ⟨.instruction (.branch f p q), v, heads⟩
        (.instruction (if f v then p else q)) v rfl hc ht R hp
  | goto f v heads =>
      apply TransitionRules.plain h.tm A.structureValue A.tuple R
      exact PlainClosure.derives h d A hn ⟨.instruction (.goto f), v, heads⟩ (.boundary (some (f v))) v rfl hc ht R hp
  | halt v heads =>
      apply TransitionRules.plain h.tm A.structureValue A.tuple R
      exact PlainClosure.derives h d A hn ⟨.instruction .halt, v, heads⟩ (.boundary none) v rfl hc ht R hp

/-- The separate record rule derives every node emitted by a bounded step. -/
theorem added {t : Nat}
    (cfg : NodeMachine.Cfg h.tm.Γ h.tm.Λ h.tm.σ
      (TimedNodes.Node (InputSegments.Identifier σ m A.structureValue.size)))
    (r : TimedNodes.Node (InputSegments.Identifier σ m A.structureValue.size) × Sigma h.tm.Γ ×
      Option (TimedNodes.Node (InputSegments.Identifier σ m A.structureValue.size)))
    (ha : NodeMachine.added (.inr t) cfg = some r)
    (hc : cfg.cursor ∈ TM2MicroSupport.controls h.tm)
    (ht : t + 1 < A.structureValue.size ^ d)
    (R : Set (Fin (TraceCodes.arity h.tm σ d) → Fin A.structureValue.size))
    (hp : TraceCodes.code h.tm d A hn (.config t cfg) ∈ R) :
    TraceCodes.code h.tm d A hn (.node r) ∈
      ParameterizedRules.operator (TransitionRules.rules h.tm σ m d (TraceCodes.nodeWidth σ d))
        A.structureValue A.tuple R := by
  cases cfg with
  | mk c v heads =>
      cases c with
      | boundary l => cases ha
      | instruction q =>
          cases q with
          | push k f q =>
              cases ha
              apply TransitionRules.push h.tm true A.structureValue A.tuple R
              exact PushClosure.derives h d A hn ⟨.instruction (.push k f q), v, heads⟩
                ⟨k, f v, .instruction q⟩ true rfl hc ht R hp
          | pop | peek | load | branch | goto | halt => cases ha

end Lax979537Proofs.TransitionDerivation
