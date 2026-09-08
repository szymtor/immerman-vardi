import Lax979537Proofs.InputBitFormulas

open Lax979537.OrderedStructures Lax979537.StructureEncoding
open Lax979537Proofs
open InputSegments InputTupleCodes InputPositionFormulas InputBitFormulas

namespace InputInterpretationTest

def exampleInput : PointedStructure [0, 1] 2 :=
  ⟨⟨8, fun r => by
    refine Fin.cases (fun _ => true) ?_ r
    intro j
    change Fin 1 at j
    have : j = 0 := Subsingleton.elim _ _
    subst j
    change (Fin 1 → Fin 8) → Bool
    exact fun x => decide ((x 0).val % 2 = 0)⟩, ![0, 7]⟩

/-- Includes a nullary relation, an alternating unary table, an empty unary
query segment, and a maximal query coordinate. -/
example : word exampleInput =
    List.replicate 8 true ++ [false, true] ++
      [true, false, true, false, true, false, true, false] ++
      [false] ++ List.replicate 7 true ++ [false] := by decide

example : (positions exampleInput).length = 27 := by decide

example : locals exampleInput (.coordinate 0) = [] := by decide

def emptyInput : PointedStructure [0, 1] 0 :=
  ⟨⟨0, fun r => by
    refine Fin.cases (fun _ => true) ?_ r
    intro j
    change Fin 1 at j
    have : j = 0 := Subsingleton.elim _ _
    subst j
    change (Fin 1 → Fin 0) → Bool
    exact fun x => Fin.elim0 (x 0)⟩, Fin.elim0⟩

/-- Empty universes retain the header delimiter and the nullary table bit. -/
example : word emptyInput = [false, true] := by decide

example : (positions emptyInput).Nodup := positions_nodup _

example (i : Fin (encode exampleInput).length) :
    bit exampleInput (ids exampleInput i).1 (ids exampleInput i).2 =
      (encode exampleInput).get i := ids_bit _ _

example : Function.Injective
    (code (σ := [0, 1]) (m := 2) (n := 8) (by decide) arity_le_width) :=
  code_injective _ _

/-- The formula bridge is uniform over vocabulary, query arity, relation
contents, and every sufficiently large finite ordered universe. -/
example {σ : Vocabulary} {m v : Nat} (query : Fin m → Fin v)
    (addr : Fin (width σ + 1) → Fin v) (b : Bool) (A : OrderedStructure σ)
    (hn : tagBound σ m ≤ A.size) (a : Fin v → Fin A.size) :
    Lax979537.FixedPointSemantics.eval (hasBit (ρ := []) arity_le_width query addr b) A a
      (fun i => Fin.elim0 i) ↔
    ∃ p ∈ positions ⟨A, a ∘ query⟩,
      code hn arity_le_width p = a ∘ addr ∧ bit ⟨A, a ∘ query⟩ p.1 p.2 = b :=
  eval_hasBit _ _ _ _ _ _ _ _

#print axioms InputSegments.word_eq_encode
#print axioms InputSegments.ids_injective
#print axioms InputSegments.ids_bit
#print axioms InputTupleCodes.code_injective
#print axioms InputPositionFormulas.eval_position
#print axioms InputBitFormulas.eval_hasBit

end InputInterpretationTest
