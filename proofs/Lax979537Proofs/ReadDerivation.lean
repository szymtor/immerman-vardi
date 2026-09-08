import Lax979537Proofs.TransitionRules

namespace Lax979537Proofs.ReadDerivation

open Turing Lax979537.OrderedStructures

theorem read_none {Node Symbol : Type} (H : PersistentStack.Heap Node Symbol)
    (head parent : Option Node) : PersistentStack.Read H head none parent ↔ head = none ∧ parent = none := by
  simp [PersistentStack.Read]

theorem read_some {Node Symbol : Type} (H : PersistentStack.Heap Node Symbol)
    (head parent : Option Node) (a : Symbol) :
    PersistentStack.Read H head (some a) parent ↔ ∃ key, head = some key ∧ (key, a, parent) ∈ H := by
  simp [PersistentStack.Read]

variable {f : List Bool → Bool} (h : TM2ComputableInPolyTime id (fun b : Bool => [b]) f)
    {σ : Vocabulary} {m : Nat} (d : Nat) (A : PointedStructure σ m)
    (hn : TraceCodes.threshold h.tm σ m ≤ A.structureValue.size)

/-- Every represented read uses either the empty rule or one of the
finitely enumerated supported-symbol rules. -/
theorem derives {t : Nat}
    (H : NodeMachine.Records (TimedNodes.Node (InputSegments.Identifier σ m A.structureValue.size)) h.tm.Γ)
    (cfg : NodeMachine.Cfg h.tm.Γ h.tm.Λ h.tm.σ
      (TimedNodes.Node (InputSegments.Identifier σ m A.structureValue.size)))
    (e : ReadEffects.Effect h.tm) (a : Option (h.tm.Γ e.key))
    (parent : Option (TimedNodes.Node (InputSegments.Identifier σ m A.structureValue.size)))
    (htarget : ReadEffects.target h.tm cfg.cursor cfg.var = some e)
    (hread : PersistentStack.Read H (cfg.heads e.key) (a.map (Sigma.mk e.key)) parent)
    (hc : cfg.cursor ∈ TM2MicroSupport.controls h.tm)
    (ht : t + 1 < A.structureValue.size ^ d)
    (R : Set (Fin (TraceCodes.arity h.tm σ d) → Fin A.structureValue.size))
    (hp : TraceCodes.code h.tm d A hn (.config t cfg) ∈ R)
    (hsupport : ∀ r ∈ H, r.2.1 ∈ TM2Alphabet.alphabet h.tm)
    (hrecords : ∀ r ∈ H, TraceCodes.code h.tm d A hn (.node r) ∈ R) :
    TraceCodes.code h.tm d A hn
        (.config (t + 1) ⟨e.next, e.state a, ReadEffects.nextHeads e cfg.heads parent⟩) ∈
      ParameterizedRules.operator (TransitionRules.rules h.tm σ m d (TraceCodes.nodeWidth σ d))
        A.structureValue A.tuple R := by
  cases a with
  | none =>
      obtain ⟨hempty, rfl⟩ := (read_none H (cfg.heads e.key) parent).mp hread
      have hh : ReadEffects.nextHeads e cfg.heads none = cfg.heads := by
        unfold ReadEffects.nextHeads
        split
        · rw [← hempty, Function.update_eq_self]
        · rfl
      rw [hh]
      apply TransitionRules.empty h.tm A.structureValue A.tuple R
      exact EmptyReadClosure.derives h d A hn cfg e htarget hempty hc ht R hp
  | some a =>
      obtain ⟨key, hhead, hr⟩ := (read_some H (cfg.heads e.key) parent (Sigma.mk e.key a)).mp hread
      apply TransitionRules.nonempty h.tm A.structureValue A.tuple R
      exact NonemptyReadClosure.derives h d A hn cfg e a key parent htarget hhead
        (hsupport _ hr) hc ht R hp (hrecords _ hr)

end Lax979537Proofs.ReadDerivation
