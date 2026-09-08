import Lax979537Proofs.FormulaProgram
import Lax979537Proofs.TupleCoordinates

namespace Lax979537Proofs.FormulaProgram

open Lax979537.OrderedStructures Lax979537.FixedPointSyntax StackBoolean

variable {K Aux : Type} [DecidableEq K] {σ : Vocabulary} {m k : Nat} {ρ : List Nat}

/-- Only the domain and relation tables need distinct input ports. Repeated
element variables and repeated arguments are permitted. -/
def Inputs.Safe (input : Inputs K σ m ρ) : Prop :=
  (∀ r, input.domain ≠ input.symbol r) ∧ ∀ r, input.domain ≠ input.relation r

def Inputs.Fresh (input : Inputs K σ m ρ) (key : K) : Prop :=
  key ≠ input.domain ∧ (∀ i, key ≠ input.element i) ∧
    (∀ r, key ≠ input.symbol r) ∧ ∀ r, key ≠ input.relation r

def ValidWork {φ : RawFormula σ m ρ} (input : Inputs K σ m ρ) (work : Work φ → K) : Prop :=
  Function.Injective work ∧ ∀ w, input.Fresh (work w)

def Clean {W : Type} (work : W → K) (s : EvalStore K Aux) : Prop :=
  ∀ w, s.stk (work w) = []

structure Represents (input : Inputs K σ m ρ) (A : OrderedStructure σ)
    (v : Fin m → Fin A.size) (η : TableEvaluation.TableEnv A.size ρ)
    (s : EvalStore K Aux) : Prop where
  domain : s.stk input.domain = List.replicate A.size true
  element : ∀ i, s.stk (input.element i) = List.replicate (v i).val true
  symbol : ∀ r, s.stk (input.symbol r) =
    (Lax979537.StructureEncoding.tuples A.size (σ.get r)).map (A.relation r)
  relation : ∀ r, s.stk (input.relation r) = DenseTables.dense (η r)

omit [DecidableEq K] in
theorem Inputs.Fresh.existsPorts {input : Inputs K σ m ρ} {key coordinate : K}
    (h : input.Fresh key) (hc : key ≠ coordinate) : (input.existsPorts coordinate).Fresh key := by
  refine ⟨h.1, ?_, h.2.2.1, h.2.2.2⟩
  intro i
  exact Fin.cases hc (fun j => h.2.1 j) i

omit [DecidableEq K] in
theorem Inputs.Fresh.lfpPorts {input : Inputs K σ m ρ} {key current : K}
    {coordinates : Fin k → K} (h : input.Fresh key)
    (hc : ∀ i, key ≠ coordinates i) (hr : key ≠ current) :
    (input.lfpPorts coordinates current).Fresh key := by
  refine ⟨h.1, ?_, h.2.2.1, ?_⟩
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa [Inputs.lfpPorts] using hc j
    · simpa [Inputs.lfpPorts] using h.2.1 j
  · intro r
    exact Fin.cases hr (fun j => h.2.2.2 j) r

omit [DecidableEq K] in
theorem Inputs.Safe.existsPorts {input : Inputs K σ m ρ} (h : input.Safe) (coordinate : K) :
    (input.existsPorts coordinate).Safe := h

omit [DecidableEq K] in
theorem Inputs.Safe.lfpPorts {input : Inputs K σ m ρ} (h : input.Safe)
    (coordinates : Fin k → K) (current : K) (hc : input.domain ≠ current) :
    (input.lfpPorts coordinates current).Safe := by
  refine ⟨h.1, ?_⟩
  intro r
  exact Fin.cases hc (fun j => h.2 j) r

omit [DecidableEq K] in
theorem Represents.of_stacks {input : Inputs K σ m ρ} {A : OrderedStructure σ}
    {v : Fin m → Fin A.size} {η : TableEvaluation.TableEnv A.size ρ} {s t : EvalStore K Aux}
    (h : Represents input A v η s) (hs : t.stk = s.stk) : Represents input A v η t := by
  constructor
  · simpa only [hs] using h.domain
  · simpa only [hs] using h.element
  · simpa only [hs] using h.symbol
  · simpa only [hs] using h.relation

omit [DecidableEq K] in
theorem Represents.result {input : Inputs K σ m ρ} {A : OrderedStructure σ}
    {v : Fin m → Fin A.size} {η : TableEvaluation.TableEnv A.size ρ} {s : EvalStore K Aux}
    (h : Represents input A v η s) (b : Bool) : Represents input A v η (result b s) :=
  h.of_stacks rfl

omit [DecidableEq K] in
theorem Represents.frame {input : Inputs K σ m ρ} {A : OrderedStructure σ}
    {v : Fin m → Fin A.size} {η : TableEvaluation.TableEnv A.size ρ} {s t : EvalStore K Aux}
    (h : Represents input A v η s) (hs : ∀ key, ¬ input.Fresh key → t.stk key = s.stk key) :
    Represents input A v η t := by
  constructor
  · rw [hs input.domain (by simp [Inputs.Fresh])]; exact h.domain
  · intro i
    rw [hs (input.element i) (by intro hf; exact hf.2.1 i rfl)]; exact h.element i
  · intro r
    rw [hs (input.symbol r) (by intro hf; exact hf.2.2.1 r rfl)]; exact h.symbol r
  · intro r
    rw [hs (input.relation r) (by intro hf; exact hf.2.2.2 r rfl)]; exact h.relation r

theorem Represents.setStack {input : Inputs K σ m ρ} {A : OrderedStructure σ}
    {v : Fin m → Fin A.size} {η : TableEvaluation.TableEnv A.size ρ} {s : EvalStore K Aux}
    (h : Represents input A v η s) {key : K} (hf : input.Fresh key) (bits : List Bool) :
    Represents input A v η (StackTuples.setStack s key bits) := by
  apply h.frame
  intro j hj
  have hne : j ≠ key := by rintro rfl; exact hj hf
  simp [StackTuples.setStack, hne]

theorem Represents.saved {input : Inputs K σ m ρ} {A : OrderedStructure σ}
    {v : Fin m → Fin A.size} {η : TableEvaluation.TableEnv A.size ρ} {s : EvalStore K Aux}
    (h : Represents input A v η s) {key : K} (hf : input.Fresh key) (b : Bool) :
    Represents input A v η (saved key b s) :=
  (h.result b).setStack hf (b :: s.stk key)

omit [DecidableEq K] in
theorem Represents.existsPorts {input : Inputs K σ m ρ} {A : OrderedStructure σ}
    {v : Fin m → Fin A.size} {η : TableEvaluation.TableEnv A.size ρ} {s : EvalStore K Aux}
    (h : Represents input A v η s) (coordinate : K) (a : Fin A.size)
    (hc : s.stk coordinate = List.replicate a.val true) :
    Represents (input.existsPorts coordinate) A (Fin.cons a v) η s := by
  refine ⟨h.domain, ?_, h.symbol, h.relation⟩
  intro i
  exact Fin.cases hc (fun j => h.element j) i

omit [DecidableEq K] in
theorem Represents.lfpPorts {input : Inputs K σ m ρ} {A : OrderedStructure σ}
    {v : Fin m → Fin A.size} {η : TableEvaluation.TableEnv A.size ρ} {s : EvalStore K Aux}
    (h : Represents input A v η s) (coordinates : Fin k → K) (current : K)
    (a : Fin k → Fin A.size) (R : TableEvaluation.Table A.size k)
    (hc : ∀ i, s.stk (coordinates i) = List.replicate (a i).val true)
    (hr : s.stk current = DenseTables.dense R) :
    Represents (input.lfpPorts coordinates current) A (Fin.append a v) (Fin.cons R η) s := by
  refine ⟨h.domain, ?_, h.symbol, ?_⟩
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa [Inputs.lfpPorts] using hc j
    · simpa [Inputs.lfpPorts] using h.element j
  · intro r
    exact Fin.cases hr (fun j => h.relation j) r

omit [DecidableEq K] in
theorem Clean.result {W : Type} {work : W → K} {s : EvalStore K Aux}
    (h : Clean work s) (b : Bool) : Clean work (result b s) := h

theorem Clean.setStack {W : Type} {work : W → K} {s : EvalStore K Aux}
    (h : Clean work s) (key : K) (hf : ∀ w, work w ≠ key) (bits : List Bool) :
    Clean work (StackTuples.setStack s key bits) := by
  intro w
  simpa [StackTuples.setStack, hf w] using h w

theorem Clean.saved {W : Type} {work : W → K} {s : EvalStore K Aux}
    (h : Clean work s) (key : K) (hf : ∀ w, work w ≠ key) (b : Bool) :
    Clean work (saved key b s) := (h.result b).setStack key hf _

theorem Represents.pack {α : Type} {input : Inputs K σ m ρ} {A : OrderedStructure σ}
    {v : Fin m → Fin A.size} {η : TableEvaluation.TableEnv A.size ρ}
    (base : α → EvalStore K Aux) (counter coordinate : K)
    (hf : input.Fresh counter) (hg : input.Fresh coordinate)
    (a : α) (i remaining : Nat) (scratch : Option Bool)
    (h : Represents input A v η (base a)) :
    Represents input A v η (StackFor.pack base counter coordinate a i remaining scratch) := by
  apply h.frame
  intro key hk
  apply StackTuples.pack_fresh
  · rintro rfl; exact hk hf
  · rintro rfl; exact hk hg

theorem Represents.packTuple {α : Type} {input : Inputs K σ m ρ} {A : OrderedStructure σ}
    {v : Fin m → Fin A.size} {η : TableEvaluation.TableEnv A.size ρ}
    (base : α → EvalStore K Aux) (slots : List (K × K))
    (hf : ∀ key ∈ StackTuples.ports slots, input.Fresh key)
    (a : α) (values remaining : List Nat) (scratch : Option Bool)
    (h : Represents input A v η (base a)) :
    Represents input A v η (StackTuples.packTuple base slots a values remaining scratch) := by
  apply h.frame
  intro key hk
  apply StackTuples.packTuple_fresh
  intro hm
  exact hk (hf key hm)

theorem Clean.pack {α W : Type} {work : W → K} (base : α → EvalStore K Aux)
    (counter coordinate : K) (hf : ∀ w, work w ≠ counter) (hg : ∀ w, work w ≠ coordinate)
    (a : α) (i remaining : Nat) (scratch : Option Bool) (h : Clean work (base a)) :
    Clean work (StackFor.pack base counter coordinate a i remaining scratch) := by
  intro w
  rw [StackTuples.pack_fresh base counter coordinate (work w) (hf w) (hg w)]
  exact h w

theorem Clean.packTuple {α W : Type} {work : W → K} (base : α → EvalStore K Aux)
    (slots : List (K × K)) (hf : ∀ w, work w ∉ StackTuples.ports slots)
    (a : α) (values remaining : List Nat) (scratch : Option Bool) (h : Clean work (base a)) :
    Clean work (StackTuples.packTuple base slots a values remaining scratch) := by
  intro w
  rw [StackTuples.packTuple_fresh base slots (work w) (hf w)]
  exact h w

end Lax979537Proofs.FormulaProgram
