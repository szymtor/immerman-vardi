import Lax751879Proofs.TransitionClosure

open Turing Lax751879Proofs Lax751879.OrderedStructures

namespace TransitionRulesTest

@[reducible] def Alphabet (k : Fin 2) : Type := if k = 0 then Bool else Nat
def readSeven (_ : Bool) (a : Option Nat) : Bool := a == some 7
def tailCode : TM2.Stmt Alphabet (Fin 1) Bool :=
  .peek 1 readSeven (.pop 1 readSeven .halt)
def code : TM2.Stmt Alphabet (Fin 1) Bool :=
  .push 1 (fun b => (if b then 7 else 13 : Nat)) tailCode

@[reducible] def tm : FinTM2 where
  K := Fin 2
  k₀ := 0
  k₁ := 0
  Γ := Alphabet
  Λ := Fin 1
  main := 0
  σ := Bool
  initialState := false
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := fun _ => code

def pushedNumber (e : PushEffects.Effect tm) : Nat :=
  if hk : e.key = (1 : Fin 2) then cast (congrArg Alphabet hk) e.symbol else 0

-- The internal alphabet is Nat, but the finite-state instruction produces
-- different supported values on the two branches.
#guard (PushEffects.target tm (.instruction code) true).map pushedNumber = some 7
#guard (PushEffects.target tm (.instruction code) false).map pushedNumber = some 13

def heads (k : Fin 2) : Option (TimedNodes.Node (Fin 2)) := some (.inl k)
def parent : Option (TimedNodes.Node (Fin 2)) := some (.inr 8)

-- Pop advances just the selected stack; peek retains its current head.
#guard (ReadEffects.target tm (.instruction (.pop 1 readSeven .halt)) false).map
  (fun e => ReadEffects.nextHeads (tm := tm) e heads parent (1 : Fin 2)) = some parent
#guard (ReadEffects.target tm (.instruction (.pop 1 readSeven .halt)) false).map
  (fun e => ReadEffects.nextHeads (tm := tm) e heads parent (0 : Fin 2)) = some (heads 0)
#guard (ReadEffects.target tm (.instruction (.peek 1 readSeven .halt)) false).map
  (fun e => ReadEffects.nextHeads (tm := tm) e heads parent (1 : Fin 2)) = some (heads 1)

/-- Configuration premises alone cannot enable a nonempty read: an actual
node record is required, even if arbitrary configuration-tagged tuples exist. -/
example (tm : FinTM2) {σ : Vocabulary} {m d w : Nat} (A : OrderedStructure σ)
    (hn : MachineConstants.bound tm ≤ A.size) (q : Fin m → Fin A.size)
    (R : Set (Fin (FactCodes.payloadWidth tm d w + 1) → Fin A.size))
    (hR : ∀ a ∈ R, (a 0).val = 0)
    (out : Fin (FactCodes.payloadWidth tm d w + 1) → Fin A.size) :
    out ∉ ParameterizedRules.operator (NonemptyReadRules.rules tm σ m d w) A q R := by
  intro ho
  obtain ⟨c, _, v, e, _, a, _, x, y, heads, parent, _, _, _, hr⟩ :=
    (NonemptyReadRules.operator_iff tm A hn q R out).mp ho
  have he : (1 : Nat) = 0 := hR _ hr
  cases he

#print axioms PushEffects.target_step
#print axioms PushRules.operator_iff
#print axioms PushClosure.preserves
#print axioms PushClosure.derives
#print axioms ReadSymbols.mem_values
#print axioms EmptyReadRules.operator_iff
#print axioms EmptyReadClosure.preserves
#print axioms EmptyReadClosure.derives
#print axioms NonemptyReadRules.operator_iff
#print axioms ReadRecordValues.node_eq
#print axioms NonemptyReadClosure.preserves
#print axioms NonemptyReadClosure.derives
#print axioms TransitionRules.preserves
#print axioms TransitionDerivation.step
#print axioms TransitionDerivation.added
#print axioms TransitionClosure.at_time
#print axioms TransitionClosure.encoded_subset

end TransitionRulesTest
