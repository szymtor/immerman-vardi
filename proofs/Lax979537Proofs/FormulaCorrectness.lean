import Lax979537Proofs.FormulaRepresentation

namespace Lax979537Proofs.FormulaProgram

open Lax979537.OrderedStructures Lax979537.FixedPointSyntax StackBoolean

variable {K Aux : Type} [DecidableEq K] {σ : Vocabulary} {m : Nat} {ρ : List Nat}

/-- Correctness of the actual finite stack program, including its polynomial
step bound and restoration of every stack. -/
def Correct (φ : RawFormula σ m ρ) : Prop :=
  ∀ (input : Inputs K σ m ρ) (work : Work φ → K), input.Safe → ValidWork input work →
  ∀ (A : OrderedStructure σ) (v : Fin m → Fin A.size) (η : TableEvaluation.TableEnv A.size ρ)
    (s : EvalStore K Aux), Clean work s → Represents input A v η s →
    ∃ c, c ≤ (costPolynomial φ).eval A.size ∧ Returns (compile φ input work) s
      (TableEvaluation.evaluate φ A v η) c

theorem correct_truth : Correct (K := K) (Aux := Aux) (.truth : RawFormula σ m ρ) := by
  intro input work _ _ A v η s _ _
  exact ⟨1, by simp [costPolynomial], answer_returns true s⟩

theorem correct_neg {φ : RawFormula σ m ρ} (hφ : Correct (K := K) (Aux := Aux) φ) :
    Correct (K := K) (Aux := Aux) (.neg φ) := by
  intro input work hs hw A v η s hc hr
  obtain ⟨c, hbound, hp⟩ := hφ input work hs hw A v η s hc hr
  refine ⟨c + 1, ?_, negate_returns hp⟩
  simpa [costPolynomial] using Nat.add_le_add_right hbound 1

theorem correct_conj {φ ψ : RawFormula σ m ρ}
    (hφ : Correct (K := K) (Aux := Aux) φ) (hψ : Correct (K := K) (Aux := Aux) ψ) :
    Correct (K := K) (Aux := Aux) (.conj φ ψ) := by
  intro input work hs hw A v η s hc hr
  have hleft : ValidWork input (fun p => work (.left p)) :=
    ⟨fun _ _ h => BinaryWork.left.inj (hw.1 h), fun p => hw.2 (.left p)⟩
  have hright : ValidWork input (fun p => work (.right p)) :=
    ⟨fun _ _ h => BinaryWork.right.inj (hw.1 h), fun p => hw.2 (.right p)⟩
  obtain ⟨cp, hcp, hp⟩ := hφ input _ hs hleft A v η s (fun p => hc (.left p)) hr
  have hclean : Clean (fun p => work (.right p))
      (saved (work .saved) (TableEvaluation.evaluate φ A v η) s) :=
    Clean.saved (fun p => hc (.right p)) _
      (by intro p h; have he := hw.1 h; cases he) _
  obtain ⟨cq, hcq, hq⟩ := hψ input _ hs hright A v η _ hclean
    (hr.saved (hw.2 .saved) _)
  refine ⟨cp + cq + 2, ?_, binary_returns (work .saved) (· && ·) hp hq⟩
  simpa [costPolynomial] using Nat.add_le_add_right (Nat.add_le_add hcp hcq) 2

omit [DecidableEq K] in
theorem fresh_element_list {input : Inputs K σ m ρ} {W : Type} (work : W → K)
    (hf : ∀ w, input.Fresh (work w)) (ports : List W) (i : Fin m) :
    input.element i ∉ ports.map work := by
  intro hm
  obtain ⟨w, _, he⟩ := List.mem_map.mp hm
  exact (hf w).2.1 i he

theorem correct_equal (x y : Fin m) : Correct (K := K) (Aux := Aux) (.equal x y : RawFormula σ m ρ) := by
  intro input work _ hw A v η s hc hr
  have hn : [work 0, work 1, work 2, work 3].Nodup :=
    (List.nodup_map_iff hw.1).mpr (by decide : ([0, 1, 2, 3] : List (Fin 4)).Nodup)
  obtain ⟨c, hb, hp⟩ := StackAtomic.equalValue_returns (input.element x) (input.element y)
    (work 0) (work 1) (work 2) (work 3) hn
    (fresh_element_list work hw.2 [0, 1, 2, 3] x)
    (fresh_element_list work hw.2 [0, 1, 2, 3] y) s (hc 0) (hc 1) (hc 2)
  simp only [hr.element, List.length_replicate] at hb hp
  refine ⟨c, ?_, ?_⟩
  · simp [costPolynomial]
    have hx := (v x).isLt
    have hy := (v y).isLt
    omega
  · simpa [compile, TableEvaluation.evaluate, Fin.ext_iff] using hp

theorem correct_less (x y : Fin m) : Correct (K := K) (Aux := Aux) (.less x y : RawFormula σ m ρ) := by
  intro input work _ hw A v η s hc hr
  have hn : [work 0, work 1, work 2].Nodup :=
    (List.nodup_map_iff hw.1).mpr (by decide : ([0, 1, 2] : List (Fin 4)).Nodup)
  obtain ⟨c, hb, hp⟩ := StackAtomic.lessValue_returns (input.element x) (input.element y)
    (work 0) (work 1) (work 2) hn
    (fresh_element_list work hw.2 [0, 1, 2] x)
    (fresh_element_list work hw.2 [0, 1, 2] y) s (hc 0) (hc 1) (hc 2)
  simp only [hr.element, List.length_replicate] at hb hp
  refine ⟨c, ?_, ?_⟩
  · simp [costPolynomial]
    have hx := (v x).isLt
    have hy := (v y).isLt
    omega
  · simpa [compile, TableEvaluation.evaluate] using hp

omit [DecidableEq K] in
theorem lookup_separation {input : Inputs K σ m ρ} (work : Fin 4 → K)
    (hi : Function.Injective work) (hd : ∀ w, work w ≠ input.domain)
    (table : K) (ht : input.domain ≠ table) (hf : ∀ w, work w ≠ table) :
    [input.domain, table, work 0, work 1, work 2, work 3].Nodup := by
  have hn : [work 0, work 1, work 2, work 3].Nodup :=
    (List.nodup_map_iff hi).mpr (by decide : ([0, 1, 2, 3] : List (Fin 4)).Nodup)
  simpa [List.nodup_cons, ht, Ne.symm (hd 0), Ne.symm (hd 1), Ne.symm (hd 2),
    Ne.symm (hd 3), Ne.symm (hf 0), Ne.symm (hf 1), Ne.symm (hf 2), Ne.symm (hf 3)] using hn

theorem correct_relation (r : Symbol σ) (args : Fin (σ.get r) → Fin m) :
    Correct (K := K) (Aux := Aux) (.relation r args : RawFormula σ m ρ) := by
  intro input work hs hw A v η s hc hr
  obtain ⟨c, hb, hp⟩ := StackTableLookup.lookup_returns input.domain (input.symbol r)
    (work 0) (work 1) (work 2) (work 3)
    (lookup_separation work hw.1 (fun w => (hw.2 w).1) _ (hs.1 r) (fun w => (hw.2 w).2.2.1 r))
    (input.element ∘ args) (v ∘ args) (A.relation r)
    (fun i => fresh_element_list work hw.2 [0, 1, 2, 3] (args i)) s hr.domain (hr.symbol r)
    (fun i => hr.element (args i)) (hc 0) (hc 1) (hc 2) (hc 3)
  exact ⟨c, by simpa [costPolynomial, StackTableLookup.eval_costPolynomial] using hb, hp⟩

theorem correct_variable (r : Fin ρ.length) (args : Fin (ρ.get r) → Fin m) :
    Correct (K := K) (Aux := Aux) (.variable r args : RawFormula σ m ρ) := by
  intro input work hs hw A v η s hc hr
  obtain ⟨c, hb, hp⟩ := StackTableLookup.lookup_returns input.domain (input.relation r)
    (work 0) (work 1) (work 2) (work 3)
    (lookup_separation work hw.1 (fun w => (hw.2 w).1) _ (hs.2 r) (fun w => (hw.2 w).2.2.2 r))
    (input.element ∘ args) (v ∘ args) (fun a => decide (a ∈ η r))
    (fun i => fresh_element_list work hw.2 [0, 1, 2, 3] (args i)) s hr.domain (hr.relation r)
    (fun i => hr.element (args i)) (hc 0) (hc 1) (hc 2) (hc 3)
  exact ⟨c, by simpa [costPolynomial, StackTableLookup.eval_costPolynomial] using hb, hp⟩

theorem correct_exists {φ : RawFormula σ (m + 1) ρ}
    (hφ : Correct (K := K) (Aux := Aux) φ) : Correct (K := K) (Aux := Aux) (.exists' φ) := by
  intro input work hs hw A v η s hc hr
  let input' := input.existsPorts (work .coordinate)
  let work' := fun p => work (.child p)
  have hchild : ValidWork input' work' := by
    refine ⟨fun _ _ h => ExistsWork.child.inj (hw.1 h), ?_⟩
    intro p
    exact (hw.2 (.child p)).existsPorts (by intro h; have he := hw.1 h; cases he)
  have hn : [work .counter, work .coordinate, work .tmp, work .accumulator].Nodup :=
    (List.nodup_map_iff hw.1).mpr (by simp :
      ([.counter, .coordinate, .tmp, .accumulator] : List (ExistsWork (Work φ))).Nodup)
  have hsep : [input.domain, work .counter, work .coordinate, work .tmp, work .accumulator].Nodup := by
    simpa [List.nodup_cons, Ne.symm (hw.2 .counter).1, Ne.symm (hw.2 .coordinate).1,
      Ne.symm (hw.2 .tmp).1, Ne.symm (hw.2 .accumulator).1] using hn
  let b : Nat → Bool := fun i => if hi : i < A.size then
    TableEvaluation.evaluate φ A (Fin.cons ⟨i, hi⟩ v) η else false
  obtain ⟨c, hb, hp⟩ := StackExists.existsValues_returns s input.domain (work .counter)
    (work .coordinate) (work .tmp) (work .accumulator) hsep (hc .counter) (hc .coordinate) (hc .tmp)
    (compile φ input' work') b A.size ((costPolynomial φ).eval A.size) hr.domain (by
      intro i hi a remaining scratch
      let base := StackExists.payload s (work .accumulator)
      have hrbase : Represents input A v η (base a) :=
        (hr.result false).setStack (hw.2 .accumulator) (a :: s.stk (work .accumulator))
      have hrpack := hrbase.pack base (work .counter) (work .coordinate)
        (hw.2 .counter) (hw.2 .coordinate) a i remaining scratch
      have hrchild : Represents input' A (Fin.cons ⟨i, hi⟩ v) η
          (StackFor.pack base (work .counter) (work .coordinate) a i remaining scratch) :=
        hrpack.existsPorts _ ⟨i, hi⟩ (by simp [StackFor.pack, StackTransfer.working])
      have hcbase : Clean work' (base a) :=
        Clean.setStack ((Clean.result (fun p => hc (.child p)) false)) _
          (by intro p h; have he := hw.1 h; cases he) _
      have hcchild := hcbase.pack base (work .counter) (work .coordinate)
        (by intro p h; have he := hw.1 h; cases he)
        (by intro p h; have he := hw.1 h; cases he) a i remaining scratch
      obtain ⟨d, hd, hrun⟩ := hφ input' work' (hs.existsPorts _) hchild A (Fin.cons ⟨i, hi⟩ v) η
        _ hcchild hrchild
      exact ⟨d, hd, by simpa [b, hi, base] using hrun⟩)
  have he : (List.range A.size).any b = (List.finRange A.size).any
      (fun a => TableEvaluation.evaluate φ A (Fin.cons a v) η) := by
    rw [← List.map_coe_finRange_eq_range, List.any_map]
    apply List.any_congr rfl
    intro a
    simp [b, a.isLt]
  refine ⟨c, ?_, ?_⟩
  · simpa [costPolynomial] using hb
  · simpa only [compile, TableEvaluation.evaluate, he, input', work'] using hp

end Lax979537Proofs.FormulaProgram
