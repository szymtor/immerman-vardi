import Lax979537Proofs.StackReadCoordinates
import Lax979537Proofs.PolynomialBounds

namespace Lax979537Proofs.StackDecoder

open StackProgram StackTransfer StackReadRelations

variable {K Aux : Type} [DecidableEq K]

structure Layout (K : Type) where
  work : Workspace K
  tables : List (Nat × K)
  coords : List K
  table_keys : (tables.map Prod.snd).Nodup
  coord_keys : coords.Nodup
  table_fresh : ∀ r ∈ tables, Fresh work r.2
  coord_fresh : ∀ c ∈ coords, Fresh work c
  arity_bound : ∀ r ∈ tables, r.1 ≤ work.counters.length
  disjoint : ∀ c ∈ coords, ∀ r ∈ tables, c ≠ r.2

def decode (l : Layout K) : BitProgram K ((Aux × Bool) × Bool) :=
  .seq (StackCheckedUnary.parse l.work.input l.work.domain)
    (.seq (StackReadRelations.readTables l.work l.tables)
      (.seq (StackReadCoordinates.readCoords l.work l.coords)
        (StackCheckedUnary.checkEnd l.work.input)))

def finish (input : K) (s : BitStore K ((Aux × Bool) × Bool)) : BitStore K ((Aux × Bool) × Bool) :=
  ⟨((s.state.1.1, s.state.1.2 && decide (s.stk input = [])), none), s.stk⟩

def result (l : Layout K) (s : BitStore K ((Aux × Bool) × Bool)) : BitStore K ((Aux × Bool) × Bool) :=
  let n := (StackUnary.splitUnary (s.stk l.work.input)).1
  let u := StackCheckedUnary.result l.work.input l.work.domain s
  let v := StackReadRelations.result l.work n l.tables u
  finish l.work.input (StackReadCoordinates.result l.work l.coords v)

noncomputable def costPolynomial (l : Layout K) : Polynomial Nat :=
  Polynomial.C 3 * Polynomial.X + Polynomial.C 5 +
    StackReadRelations.costPolynomial l.tables +
    Polynomial.C l.coords.length * (Polynomial.C 27 * Polynomial.X + Polynomial.C 21)

theorem header_ready (w : Workspace K) (s : BitStore K ((Aux × Bool) × Bool))
    (hs : ∀ key, key ≠ w.input → s.stk key = []) :
    Ready w (StackUnary.splitUnary (s.stk w.input)).1
      (StackCheckedUnary.result w.input w.domain s) := by
  have h := w.separate
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true,
    not_or, and_true] at h
  have hd : s.stk w.domain = [] := hs _ (by tauto)
  have hp (key : K) (hi : key ≠ w.input) (hd : key ≠ w.domain) :
      (StackCheckedUnary.result w.input w.domain s).stk key = [] := by
    rw [StackCheckedUnary.result_preserves _ _ _ hi hd]
    exact hs key hi
  refine ⟨?_, hp _ (by tauto) (by tauto), hp _ (by tauto) (by tauto),
    hp _ (by tauto) (by tauto), ?_⟩
  · simp [StackCheckedUnary.result, hd]
  · intro c hm
    have hcf := w.counter_fresh c hm
    simp only [List.mem_cons, List.not_mem_nil, not_false_eq_true, not_or, and_true] at hcf
    exact hp _ (by tauto) (by tauto)

theorem header_fresh (w : Workspace K) (key : K) (hf : Fresh w key)
    (s : BitStore K ((Aux × Bool) × Bool)) (hs : ∀ key, key ≠ w.input → s.stk key = []) :
    (StackCheckedUnary.result w.input w.domain s).stk key = [] := by
  have h := hf.1
  simp only [List.mem_cons, List.not_mem_nil, not_false_eq_true, not_or, and_true] at h
  rw [StackCheckedUnary.result_preserves _ _ _ (by tauto) (by tauto)]
  exact hs key (by tauto)

/-- The assembled decoder terminates on every bit string in polynomial
machine time, retaining the decoded tables and coordinates for evaluation.
Its semantic result is explicit; identifying its validity bit with canonical
structure encodings is a separate correctness obligation. -/
theorem decode_executes (l : Layout K) (s : BitStore K ((Aux × Bool) × Bool))
    (hs : ∀ key, key ≠ l.work.input → s.stk key = []) :
    ∃ t, t ≤ (costPolynomial l).eval (s.stk l.work.input).length ∧
      Executes (decode l) s (result l s) t := by
  let n := (StackUnary.splitUnary (s.stk l.work.input)).1
  let u := StackCheckedUnary.result l.work.input l.work.domain s
  let v := StackReadRelations.result l.work n l.tables u
  let q := StackReadCoordinates.result l.work l.coords v
  have hic : l.work.input ≠ l.work.domain := by
    have h := l.work.separate
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true,
      not_or, and_true] at h
    tauto
  obtain ⟨a, ha, hp⟩ := StackCheckedUnary.parse_linear_bound l.work.input l.work.domain hic s
  have hu : Ready l.work n u := header_ready l.work s hs
  have hut : ∀ r ∈ l.tables, u.stk r.2 = [] :=
    fun r hm => header_fresh l.work r.2 (l.table_fresh r hm) s hs
  obtain ⟨b, hb, hr⟩ := StackReadRelations.readTables_executes l.work l.tables l.table_keys
    l.table_fresh l.arity_bound n u hu hut
  have hv : Ready l.work n v := StackReadRelations.tables_ready l.work n l.tables l.table_fresh u hu
  have hvc : ∀ c ∈ l.coords, v.stk c = [] := by
    intro c hm
    have hcf := (l.coord_fresh c hm).1
    simp only [List.mem_cons, List.not_mem_nil, not_false_eq_true, not_or, and_true] at hcf
    rw [StackReadRelations.result_preserves l.work n l.tables c (by tauto) (l.disjoint c hm)]
    exact header_fresh l.work c (l.coord_fresh c hm) s hs
  obtain ⟨c, hc, hq⟩ := StackReadCoordinates.readCoords_executes l.work l.coords l.coord_keys
    l.coord_fresh n v hv hvc
  have he := StackCheckedUnary.checkEnd_executes l.work.input q
  have hn : n ≤ (s.stk l.work.input).length := StackUnary.splitUnary_le _
  have hul : (u.stk l.work.input).length ≤ (s.stk l.work.input).length := by
    simpa [u, StackCheckedUnary.result, hic] using StackUnary.splitUnary_rest_le (s.stk l.work.input)
  have hvl : (v.stk l.work.input).length ≤ (s.stk l.work.input).length :=
    (StackReadRelations.input_length_le l.work n l.tables l.table_fresh u).trans hul
  have hpoly := PolynomialBounds.eval_mono (StackReadRelations.costPolynomial l.tables) hn
  have hmul := Nat.mul_le_mul_left l.coords.length
    (show 15 * (v.stk l.work.input).length + 12 * n + 21 ≤
      27 * (s.stk l.work.input).length + 21 from by omega)
  refine ⟨a + (b + (c + 1)), ?_, Executes.seq hp (Executes.seq hr (Executes.seq hq he))⟩
  simp only [costPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X]
  omega

end Lax979537Proofs.StackDecoder
