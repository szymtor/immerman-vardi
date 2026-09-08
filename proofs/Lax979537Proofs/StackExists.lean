import Lax979537Proofs.StackFor
import Lax979537Proofs.StackBoolean

namespace Lax979537Proofs.StackExists

open StackProgram StackTransfer StackBoolean StackFor

variable {K Aux : Type} [DecidableEq K]

def accumulate (acc : K) (body : EvalProgram K Aux) : EvalProgram K Aux :=
  .seq body (.seq (combine acc (· || ·)) (.seq (save acc) (answer false)))

def finish (acc : K) : EvalProgram K Aux :=
  .atom (.pop acc (fun s b => (((s.1.1.1, true), b.getD false), none)))

/-- Existential quantification by an exhaustive scan of the domain. The
program is fixed independently of the domain size and the predicate. -/
def existsValues (domain counter coord tmp acc : K) (body : EvalProgram K Aux) :
    EvalProgram K Aux :=
  .seq (answer false) (.seq (save acc)
    (.seq (forValues domain counter coord tmp (accumulate acc body)) (finish acc)))

def payload (s : EvalStore K Aux) (acc : K) (a : Bool) : EvalStore K Aux :=
  ⟨(result false s).state, Function.update s.stk acc (a :: s.stk acc)⟩

theorem accumulate_returns (s : EvalStore K Aux) (counter coord acc : K)
    (hca : counter ≠ acc) (hxa : coord ≠ acc)
    (body : EvalProgram K Aux) (a b : Bool) (i remaining cost : Nat) (scratch : Option Bool)
    (h : Returns body (pack (payload s acc) counter coord a i remaining scratch) b cost) :
    Executes (accumulate acc body)
      (pack (payload s acc) counter coord a i remaining scratch)
      (pack (payload s acc) counter coord (a || b) i remaining none) (cost + 3) := by
  let t := pack (payload s acc) counter coord a i remaining scratch
  have ha : t.stk acc = a :: s.stk acc := by
    simp [t, pack, working, payload, Ne.symm hca, Ne.symm hxa]
  have hc := Executes.atom
    (.pop acc (fun v : ((Aux × Bool) × Bool) × Option Bool => fun x =>
      (((v.1.1.1, true), x.getD false || v.1.2), none))) (result b t)
  have hs := Executes.atom (.push acc (fun v : ((Aux × Bool) × Bool) × Option Bool => v.1.2))
    (Op.apply (.pop acc (fun v x => (((v.1.1.1, true), x.getD false || v.1.2), none))) (result b t))
  have hz := answer_returns false
    (Op.apply (.push acc (fun v : ((Aux × Bool) × Bool) × Option Bool => v.1.2))
      (Op.apply (.pop acc (fun v x => (((v.1.1.1, true), x.getD false || v.1.2), none))) (result b t)))
  have hh := Executes.seq h (Executes.seq hc (Executes.seq hs hz))
  have he : result false
      (Op.apply (.push acc (fun v : ((Aux × Bool) × Bool) × Option Bool => v.1.2))
        (Op.apply (.pop acc (fun v x => (((v.1.1.1, true), x.getD false || v.1.2), none))) (result b t))) =
      pack (payload s acc) counter coord (a || b) i remaining none := by
    apply Store.ext
    · rfl
    · funext key
      by_cases hk : key = acc
      · subst key; simp [Op.apply, result, ha, pack, payload, working, Ne.symm hca, Ne.symm hxa]
      · simp [Op.apply, result, Function.update_apply, t, pack, payload, working, hk]
  rw [he] at hh
  simpa only [Nat.add_assoc] using hh

theorem fold_or (b : Nat → Bool) (start count : Nat) (a : Bool) :
    foldRange (fun i a => a || b i) start count a =
      (a || (List.range' start count).any b) := by
  induction count generalizing start a with
  | zero => simp [foldRange]
  | succ count ih => simp [foldRange, ih, List.range'_succ, Bool.or_assoc]

/-- A bounded evaluator for each valid element yields a bounded evaluator
for its existential quantification, restoring all stacks including acc. -/
theorem existsValues_returns (s : EvalStore K Aux) (domain counter coord tmp acc : K)
    (hsep : [domain, counter, coord, tmp, acc].Nodup)
    (hc : s.stk counter = []) (hx : s.stk coord = []) (ht : s.stk tmp = [])
    (body : EvalProgram K Aux) (b : Nat → Bool) (n B : Nat)
    (hd : s.stk domain = List.replicate n true)
    (hbody : ∀ i, i < n → ∀ a remaining scratch,
      ∃ cost, cost ≤ B ∧ Returns body
        (pack (payload s acc) counter coord a i remaining scratch) (b i) cost) :
    ∃ cost, cost ≤ (B + 15) * n + 11 ∧
      Returns (existsValues domain counter coord tmp acc body) s ((List.range n).any b) cost := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true,
    not_or, and_true] at hsep
  have hca : counter ≠ acc := by tauto
  have hxa : coord ≠ acc := by tauto
  have hta : tmp ≠ acc := by tauto
  have hda : domain ≠ acc := by tauto
  have hfour : [domain, counter, coord, tmp].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true,
      not_or, and_true]
    tauto
  obtain ⟨c, hbound, hfor⟩ := forValues_executes (payload s acc) domain counter coord tmp hfour
    (accumulate acc body) (fun i a => a || b i) n (B + 3)
    (by intro a; simpa [payload, hca] using hc)
    (by intro a; simpa [payload, hxa] using hx)
    (by intro a; simpa [payload, hta] using ht)
    (by
      intro i hi a remaining scratch
      obtain ⟨c, hc, hp⟩ := hbody i hi a remaining scratch
      exact ⟨c + 3, none, by omega,
        accumulate_returns s counter coord acc hca hxa body a (b i) i remaining c scratch hp⟩)
    false (by simpa [payload, hda] using hd)
  rw [fold_or] at hfor
  simp only [Bool.false_or, ← List.range_eq_range'] at hfor
  have hs : Executes (save acc) (result false s) (payload s acc false) 1 := Executes.atom _ _
  have hf := Executes.atom
    (.pop acc (fun v : ((Aux × Bool) × Bool) × Option Bool => fun x =>
      (((v.1.1.1, true), x.getD false), none)))
    (reset (payload s acc ((List.range n).any b)))
  have he : Op.apply (.pop acc (fun v : ((Aux × Bool) × Bool) × Option Bool => fun x =>
      (((v.1.1.1, true), x.getD false), none)))
      (reset (payload s acc ((List.range n).any b))) = result ((List.range n).any b) s := by
    apply Store.ext
    · simp [Op.apply, reset, payload, result]
    · simp [Op.apply, reset, payload, result, Function.update_idem]
  rw [he] at hf
  have hn : B + 3 + 12 = B + 15 := by omega
  rw [hn] at hbound
  exact ⟨1 + (1 + (c + 1)), by omega,
    Executes.seq (answer_returns false s) (Executes.seq hs (Executes.seq hfor hf))⟩

theorem any_range_iff (b : Nat → Bool) (n : Nat) :
    (List.range n).any b = true ↔ ∃ i, i < n ∧ b i = true := by simp

end Lax979537Proofs.StackExists
