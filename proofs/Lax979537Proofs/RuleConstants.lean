import Lax979537Proofs.ParameterizedRules
import Lax979537Proofs.AddressFormulas

namespace Lax979537Proofs.RuleConstants

open Lax979537.OrderedStructures Lax979537.FixedPointSyntax
open Lax979537.FixedPointSemantics
open FormulaMacros TupleOrder SyntaxOperations AddressFormulas

/-- A tuple pattern may refer to a fixed block of numeral constants followed
by its data variables. The compiler supplies the actual first-order bindings. -/
structure Template (σ : Vocabulary) (m k C : Nat) where
  numVars : Nat
  guard : RawFormula σ numVars []
  guard_firstOrder : FirstOrder guard
  parameters : Fin m → Fin numVars
  head : Fin k → Fin (C + numVars)
  premises : List (Fin k → Fin (C + numVars))

def compile {σ : Vocabulary} {m k C : Nat} (r : Template σ m k C) : ParameterizedRules.Rule σ m k where
  numVars := C + r.numVars
  guard := .conj
    (allOf ((List.finRange C).map fun i => numeral i.val (Fin.castAdd r.numVars i)))
    (rename r.guard (Fin.natAdd C))
  guard_firstOrder := by
    refine ⟨?_, (firstOrder_rename _ _).mpr r.guard_firstOrder⟩
    simp only [firstOrder_allOf, List.forall_mem_map]
    exact fun i _ => numeral_firstOrder _ _
  parameters := Fin.natAdd C ∘ r.parameters
  head := r.head
  premises := r.premises

def assignment {C n v : Nat} (hn : C ≤ n) (a : Fin v → Fin n) : Fin (C + v) → Fin n :=
  Fin.append (Fin.castLE hn) a

theorem assignment_data {C n v : Nat} (hn : C ≤ n) (a : Fin v → Fin n) :
    assignment hn a ∘ Fin.natAdd C = a := by funext i; simp [assignment]

theorem assignment_unique {C n v : Nat} (hn : C ≤ n) (a : Fin (C + v) → Fin n)
    (hc : ∀ i : Fin C, (a (Fin.castAdd v i)).val = i.val) :
    a = assignment hn (a ∘ Fin.natAdd C) := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    apply Fin.ext
    simpa [assignment] using hc j
  · intro j; simp [assignment]

def holds {σ : Vocabulary} {m k C : Nat} (r : Template σ m k C)
    (A : OrderedStructure σ) (hn : C ≤ A.size) (q : Fin m → Fin A.size)
    (R : Set (Fin k → Fin A.size)) (a : Fin k → Fin A.size) : Prop :=
  ∃ v : Fin r.numVars → Fin A.size,
    eval r.guard A v (fun i => Fin.elim0 i) ∧ v ∘ r.parameters = q ∧
      assignment hn v ∘ r.head = a ∧ ∀ b ∈ r.premises, assignment hn v ∘ b ∈ R

/-- Constants in the tuple patterns have their literal numeral values;
all other witnesses are precisely the data variables of the template. -/
theorem compile_holds {σ : Vocabulary} {m k C : Nat} (r : Template σ m k C)
    (A : OrderedStructure σ) (hn : C ≤ A.size) (q : Fin m → Fin A.size)
    (R : Set (Fin k → Fin A.size)) (a : Fin k → Fin A.size) :
    (compile r).holds A q R a ↔ holds r A hn q R a := by
  simp only [ParameterizedRules.Rule.holds, compile, eval, eval_allOf,
    List.forall_mem_map, List.mem_finRange, forall_const, eval_numeral, eval_rename]
  constructor
  · rintro ⟨v, ⟨hc, hg⟩, hq, ha, hp⟩
    have he := assignment_unique hn v hc
    refine ⟨v ∘ Fin.natAdd C, hg, hq, ?_, ?_⟩
    · rw [← he]; exact ha
    · rw [← he]; exact hp
  · rintro ⟨v, hg, hq, ha, hp⟩
    refine ⟨assignment hn v, ⟨?_, ?_⟩, ?_, ha, hp⟩
    · intro i; simp [assignment]
    · rw [assignment_data]; exact hg
    · simpa only [← Function.comp_assoc, assignment_data] using hq

end Lax979537Proofs.RuleConstants
