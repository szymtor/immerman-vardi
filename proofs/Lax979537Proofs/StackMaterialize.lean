import Lax979537Proofs.StackTuples
import Lax979537Proofs.StackBoolean

namespace Lax979537Proofs.StackMaterialize

open StackProgram StackTransfer StackFor StackTuples StackBoolean

variable {K Aux : Type} [DecidableEq K]

def emit (rev : K) (body : EvalProgram K Aux) : EvalProgram K Aux :=
  .seq body (.seq (save rev) (answer false))

def materialize (domain tmp rev out : K) (slots : List (K × K))
    (body : EvalProgram K Aux) : EvalProgram K Aux :=
  .seq (answer false) (.seq (forTuples domain tmp (emit rev body) slots) (transfer rev out))

def payload (s : EvalStore K Aux) (rev : K) (bits : List Bool) : EvalStore K Aux :=
  setStack (result false s) rev (bits ++ s.stk rev)

theorem emit_executes (s : EvalStore K Aux) (rev : K) (slots : List (K × K))
    (hfresh : rev ∉ ports slots) (body : EvalProgram K Aux) (bits : List Bool)
    (values remaining : List Nat) (scratch : Option Bool) (b : Bool) (c : Nat)
    (hp : Returns body (packTuple (payload s rev) slots bits values remaining scratch) b c) :
    Executes (emit rev body) (packTuple (payload s rev) slots bits values remaining scratch)
      (packTuple (payload s rev) slots (b :: bits) values remaining none) (c + 2) := by
  let t := packTuple (payload s rev) slots bits values remaining scratch
  have hpack (bits : List Bool) (scratch : Option Bool) :
      packTuple (payload s rev) slots bits values remaining scratch =
        setStack (packTuple (fun _ : Unit => result false s) slots () values remaining scratch)
          rev (bits ++ s.stk rev) := by
    change packTuple (fun bits => setStack (result false s) rev (bits ++ s.stk rev))
      slots bits values remaining scratch = _
    rw [packTuple_setStack (fun _ : List Bool => result false s) slots rev hfresh, packTuple_const]
  have hs := Executes.atom (.push rev (fun v : ((Aux × Bool) × Bool) × Option Bool => v.1.2))
    (result b t)
  have hz := answer_returns false
    (Op.apply (.push rev (fun v : ((Aux × Bool) × Bool) × Option Bool => v.1.2)) (result b t))
  have he : result false
      (Op.apply (.push rev (fun v : ((Aux × Bool) × Bool) × Option Bool => v.1.2)) (result b t)) =
      packTuple (payload s rev) slots (b :: bits) values remaining none := by
    apply Store.ext
    · simp [result, Op.apply, t, packTuple_state, payload, setStack]
    · simp [result, Op.apply, t, hpack, setStack, packTuple_stk_scratch, Function.update_idem]
  have hh := Executes.seq hp (Executes.seq hs hz)
  rw [he] at hh
  simpa only [Nat.add_assoc] using hh

def table (n k : Nat) (b : List Nat → Bool) : List Bool := (tuples n k).map b

theorem table_length (n k : Nat) (b : List Nat → Bool) : (table n k b).length = n ^ k := by
  simp [table, tuples_length]

noncomputable def costPolynomial (B : Polynomial Nat) (k : Nat) : Polynomial Nat :=
  StackTuples.costPolynomial (B + 2) k + 3 * Polynomial.X ^ k + 3

theorem eval_costPolynomial (B : Polynomial Nat) (n k : Nat) :
    (costPolynomial B k).eval n = StackTuples.cost n (B.eval n + 2) k + 3 * n ^ k + 3 := by
  simp [costPolynomial, StackTuples.eval_costPolynomial]

/-- Materialize a complete dense truth table, in canonical tuple order,
while preserving input stacks and cleaning the reverse buffer and loops.
The body evaluator is used once per tuple; previous rows are stored bits. -/
theorem materialize_executes (s : EvalStore K Aux) (domain tmp rev out : K)
    (slots : List (K × K)) (hsep : (domain :: tmp :: rev :: out :: ports slots).Nodup)
    (hempty : ∀ key, key ∈ tmp :: rev :: ports slots → s.stk key = [])
    (body : EvalProgram K Aux) (b : List Nat → Bool) (n B : Nat)
    (hdomain : s.stk domain = List.replicate n true)
    (hbody : ∀ values, values.length = slots.length → (∀ i ∈ values, i < n) →
      ∀ remaining, remaining.length = slots.length → ∀ bits scratch,
      ∃ c, c ≤ B ∧ Returns body
        (packTuple (payload s rev) slots bits values remaining scratch) (b values) c) :
    ∃ c, c ≤ StackTuples.cost n (B + 2) slots.length + 3 * n ^ slots.length + 3 ∧
      Executes (materialize domain tmp rev out slots body) s
        (setStack (result false s) out (table n slots.length b ++ s.stk out)) c := by
  have hrev : s.stk rev = [] := hempty rev (by simp)
  have hfresh : rev ∉ ports slots := by
    simp only [List.nodup_cons, List.mem_cons, not_or] at hsep
    tauto
  have hro : rev ≠ out := by
    simp only [List.nodup_cons, List.mem_cons, not_or] at hsep
    tauto
  have hdr : domain ≠ rev := by
    simp only [List.nodup_cons, List.mem_cons, not_or] at hsep
    tauto
  have hloop : (domain :: tmp :: ports slots).Nodup := by
    simp only [List.nodup_cons, List.mem_cons, not_or] at hsep ⊢
    tauto
  obtain ⟨c, hc, hfor⟩ := forTuples_executes (payload s rev) domain tmp (emit rev body) slots hloop
    (by
      intro bits key hk
      have hkr : key ≠ rev := by
        simp only [List.nodup_cons, List.mem_cons, not_or] at hsep
        simp only [List.mem_cons] at hk
        rcases hk with rfl | hk
        · tauto
        · intro he; subst key; exact hfresh hk
      simp only [payload, setStack, result, Function.update_of_ne hkr]
      exact hempty key (by simp only [List.mem_cons] at hk ⊢; tauto))
    (fun values bits => b values :: bits) n (B + 2)
    (by intro bits; simpa [payload, setStack, result, hdr] using hdomain)
    (by
      intro values hlen hvalid remaining hrem bits scratch
      obtain ⟨c, hc, hp⟩ := hbody values hlen hvalid remaining hrem bits scratch
      exact ⟨c + 2, none, by omega,
        emit_executes s rev slots hfresh body bits values remaining scratch (b values) c hp⟩) []
  have hinit : payload s rev [] = result false s := by simp [payload, setStack, result]
  have hfold : foldTuples n slots.length (fun values bits => b values :: bits) [] =
      (table n slots.length b).reverse := by
    simp [foldTuples_eq_foldl, List.foldl_flip_cons_eq_append, table]
  rw [hinit, hfold] at hfor
  let t := reset (payload s rev (table n slots.length b).reverse)
  have htr := transfer_store rev out hro t
  have ht_rev : t.stk rev = (table n slots.length b).reverse := by
    simp [t, reset, payload, setStack, hrev]
  have ht_out : t.stk out = s.stk out := by
    simp [t, reset, payload, setStack, result, Ne.symm hro]
  rw [ht_rev, ht_out, List.length_reverse, table_length, List.reverse_reverse] at htr
  have he : (⟨(t.state.1, none), Function.update (Function.update t.stk rev []) out
      (table n slots.length b ++ s.stk out)⟩ : EvalStore K Aux) =
      setStack (result false s) out (table n slots.length b ++ s.stk out) := by
    apply Store.ext
    · rfl
    · simp [t, reset, payload, setStack, result, Function.update_idem, ← hrev]
  rw [he] at htr
  exact ⟨1 + (c + (3 * n ^ slots.length + 2)), by omega,
    Executes.seq (answer_returns false s) (Executes.seq hfor htr)⟩

end Lax979537Proofs.StackMaterialize
