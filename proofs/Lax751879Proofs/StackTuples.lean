import Lax751879Proofs.StackFor
import Lax751879.StructureEncoding

namespace Lax751879Proofs.StackTuples

open StackProgram StackTransfer StackFor

variable {K Aux α : Type} [DecidableEq K]

def ports (slots : List (K × K)) : List K := slots.flatMap (fun p => [p.1, p.2])

def withScratch (s : BitStore K Aux) (scratch : Option Bool) : BitStore K Aux :=
  ⟨(s.state.1, scratch), s.stk⟩

/-- Install a tuple of unary coordinates and the loop counters surrounding
the callback. This definition follows the nesting order of the program. -/
def packTuple (base : α → BitStore K Aux) : List (K × K) → α →
    List Nat → List Nat → Option Bool → BitStore K Aux
  | [], a, _, _, scratch => withScratch (base a) scratch
  | (c, x) :: slots, a, values, remaining, scratch =>
      packTuple (fun a => pack base c x a (values.headD 0) (remaining.headD 0) scratch)
        slots a values.tail remaining.tail scratch

def clearScratch : BitProgram K Aux := .atom (.load (fun s => (s.1, none)))

/-- The number of nesting levels is fixed by the arity. No domain size is
captured in a control operation or in the program syntax. -/
def forTuples (domain tmp : K) (body : BitProgram K Aux) : List (K × K) → BitProgram K Aux
  | [] => .seq body clearScratch
  | (c, x) :: slots => forValues domain c x tmp (forTuples domain tmp body slots)

def tuples (n : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | k + 1 => (List.range n).flatMap (fun i => (tuples n k).map (i :: ·))

def foldTuples (n : Nat) : Nat → (List Nat → α → α) → α → α
  | 0, f, a => f [] a
  | k + 1, f, a => foldRange (fun i a => foldTuples n k (fun xs => f (i :: xs)) a) 0 n a

def cost (n B : Nat) : Nat → Nat
  | 0 => B + 1
  | k + 1 => (cost n B k + 12) * n + 8

noncomputable def costPolynomial (B : Polynomial Nat) : Nat → Polynomial Nat
  | 0 => B + 1
  | k + 1 => (costPolynomial B k + 12) * Polynomial.X + 8

theorem eval_costPolynomial (B : Polynomial Nat) (n k : Nat) :
    (costPolynomial B k).eval n = cost n (B.eval n) k := by
  induction k with
  | zero => simp [costPolynomial, cost]
  | succ k ih => simp [costPolynomial, cost, ih]

theorem pack_fresh (base : α → BitStore K Aux) (c x key : K)
    (hc : key ≠ c) (hx : key ≠ x) (a : α) (i remaining : Nat) (scratch : Option Bool) :
    (pack base c x a i remaining scratch).stk key = (base a).stk key := by
  simp [pack, working, hc, hx]

theorem packTuple_pack_scratch (base : α → BitStore K Aux) (counter coord : K)
    (i remaining : Nat) (initial : Option Bool) (slots : List (K × K))
    (a : α) (values counters : List Nat) (scratch : Option Bool) :
    packTuple (fun a => pack base counter coord a i remaining initial) slots a values counters scratch =
      packTuple (fun a => pack base counter coord a i remaining none) slots a values counters scratch := by
  cases slots <;> rfl

/-- Nested domain loops call the body once for every tuple in lexicographic
order, then restore their entire private workspace. The callback contract
allows arbitrary payload changes and scratch values, but preserves counters. -/
theorem forTuples_executes (base : α → BitStore K Aux) (domain tmp : K)
    (body : BitProgram K Aux) (slots : List (K × K))
    (hsep : (domain :: tmp :: ports slots).Nodup)
    (hempty : ∀ a key, key ∈ tmp :: ports slots → (base a).stk key = [])
    (f : List Nat → α → α) (n B : Nat)
    (hdomain : ∀ a, (base a).stk domain = List.replicate n true)
    (hbody : ∀ values, values.length = slots.length → (∀ i ∈ values, i < n) →
      ∀ remaining, remaining.length = slots.length → ∀ a scratch,
      ∃ c scratch', c ≤ B ∧ Executes body
        (packTuple base slots a values remaining scratch)
        (packTuple base slots (f values a) values remaining scratch') c)
    (a : α) : ∃ c, c ≤ cost n B slots.length ∧
      Executes (forTuples domain tmp body slots) (base a)
        (reset (base (foldTuples n slots.length f a))) c := by
  induction slots generalizing base f a with
  | nil =>
      obtain ⟨c, scratch, hc, hp⟩ := hbody [] rfl (by simp) [] rfl a (base a).state.2
      have hz := Executes.atom (.load (fun s : Aux × Option Bool => (s.1, none)))
        (packTuple base [] (f [] a) [] [] scratch)
      exact ⟨c + 1, by simpa [cost] using Nat.add_le_add_right hc 1, Executes.seq hp hz⟩
  | cons slot slots ih =>
      rcases slot with ⟨counter, coord⟩
      have hn : (domain :: tmp :: counter :: coord :: ports slots).Nodup := hsep
      have htail : (domain :: tmp :: ports slots).Nodup := by
        simp only [List.nodup_cons, List.mem_cons, not_or] at hn ⊢
        tauto
      have hfour : [domain, counter, coord, tmp].Nodup := by
        simp only [List.nodup_cons, List.mem_cons, not_or] at hn
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true,
          not_or, and_true]
        tauto
      have hfresh (key : K) (hk : key ∈ domain :: tmp :: ports slots) :
          key ≠ counter ∧ key ≠ coord := by
        simp only [List.nodup_cons, List.mem_cons, not_or] at hn
        simp only [List.mem_cons] at hk
        rcases hk with rfl | rfl | hk
        · tauto
        · tauto
        · constructor <;> intro he <;> subst key <;> tauto
      have hcallback : ∀ i, i < n → ∀ a remaining scratch,
          ∃ c scratch', c ≤ cost n B slots.length ∧
            Executes (forTuples domain tmp body slots)
              (pack base counter coord a i remaining scratch)
              (pack base counter coord
                (foldTuples n slots.length (fun xs => f (i :: xs)) a) i remaining scratch') c := by
        intro i hi a remaining scratch
        let base' := fun a => pack base counter coord a i remaining scratch
        obtain ⟨c, hc, hp⟩ := ih base' htail
          (by
            intro a key hk
            rw [pack_fresh base counter coord key (hfresh key (by simp [hk])).1
              (hfresh key (by simp [hk])).2]
            apply hempty a key
            simp only [ports, List.flatMap_cons, List.cons_append, List.nil_append,
              List.mem_cons] at hk ⊢
            tauto)
          (fun xs => f (i :: xs))
          (by
            intro a
            rw [pack_fresh base counter coord domain (hfresh domain (by simp)).1
              (hfresh domain (by simp)).2]
            exact hdomain a)
          (by
            intro xs hxs hvalid rs hrs a scratch'
            have hp := hbody (i :: xs) (by simp [hxs])
              (by simp only [List.mem_cons, forall_eq_or_imp]; exact ⟨hi, hvalid⟩)
              (remaining :: rs) (by simp [hrs]) a scratch'
            simpa only [packTuple, List.headD_cons, List.tail_cons, base', packTuple_pack_scratch] using hp)
          a
        exact ⟨c, none, hc, hp⟩
      obtain ⟨c, hc, hp⟩ := forValues_executes base domain counter coord tmp hfour
        (forTuples domain tmp body slots)
        (fun i a => foldTuples n slots.length (fun xs => f (i :: xs)) a) n (cost n B slots.length)
        (fun a => hempty a counter (by simp [ports]))
        (fun a => hempty a coord (by simp [ports]))
        (fun a => hempty a tmp (by simp)) hcallback a (hdomain a)
      exact ⟨c, hc, hp⟩

theorem foldTuples_eq_foldl (n k : Nat) (f : List Nat → α → α) (a : α) :
    foldTuples n k f a = (tuples n k).foldl (fun a xs => f xs a) a := by
  induction k generalizing f a with
  | zero => rfl
  | succ k ih =>
      simp only [foldTuples, foldRange_zero_eq, tuples, List.foldl_flatMap, List.foldl_map]
      congr 1
      funext a i
      exact ih (fun xs => f (i :: xs)) a

def tupleValues {n k : Nat} (v : Fin k → Fin n) : List Nat := List.ofFn (fun i => (v i).val)

theorem tupleValues_cons {n k : Nat} (i : Fin n) (v : Fin k → Fin n) :
    tupleValues (Fin.cons i v) = i.val :: tupleValues v := by
  simp [tupleValues, List.ofFn_succ]

/-- The machine loop uses exactly the order chosen in the approved dense
encoding, including its unique nullary tuple. -/
theorem tuples_eq_canonical (n k : Nat) :
    tuples n k = (Lax751879.StructureEncoding.tuples n k).map tupleValues := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [tuples, Lax751879.StructureEncoding.tuples, List.map_flatMap,
        ← List.map_coe_finRange_eq_range]
      simp only [List.flatMap_map]
      congr 1
      funext i
      rw [ih]
      simp [List.map_map, Function.comp_def, tupleValues_cons]

theorem tuples_length (n k : Nat) : (tuples n k).length = n ^ k := by
  induction k with
  | zero => simp [tuples]
  | succ k ih =>
      simp [tuples, List.length_flatMap, ih, List.sum_replicate, Nat.pow_succ, Nat.mul_comm]

theorem packTuple_const (s : BitStore K Aux) (slots : List (K × K))
    (a : α) (values remaining : List Nat) (scratch : Option Bool) :
    packTuple (fun _ : α => s) slots a values remaining scratch =
      packTuple (fun _ : Unit => s) slots () values remaining scratch := by
  induction slots generalizing s values remaining with
  | nil => rfl
  | cons slot slots ih => exact ih _ _ _

theorem packTuple_state (base : α → BitStore K Aux) (slots : List (K × K))
    (a : α) (values remaining : List Nat) (scratch : Option Bool) :
    (packTuple base slots a values remaining scratch).state = ((base a).state.1, scratch) := by
  induction slots generalizing base values remaining with
  | nil => rfl
  | cons slot slots ih => exact ih _ _ _

theorem packTuple_stk_scratch (base : α → BitStore K Aux) (slots : List (K × K))
    (a : α) (values remaining : List Nat) (scratch : Option Bool) :
    (packTuple base slots a values remaining scratch).stk =
      (packTuple base slots a values remaining none).stk := by
  induction slots generalizing base values remaining with
  | nil => rfl
  | cons slot slots ih =>
      rw [packTuple, ih, packTuple_pack_scratch]
      rfl

theorem packTuple_fresh (base : α → BitStore K Aux) (slots : List (K × K))
    (key : K) (hfresh : key ∉ ports slots) (a : α) (values remaining : List Nat)
    (scratch : Option Bool) :
    (packTuple base slots a values remaining scratch).stk key = (base a).stk key := by
  induction slots generalizing base values remaining with
  | nil => rfl
  | cons slot slots ih =>
      rcases slot with ⟨counter, coord⟩
      have h : key ≠ counter ∧ key ≠ coord ∧ key ∉ ports slots := by simpa [ports] using hfresh
      rw [packTuple, ih _ h.2.2, pack_fresh base counter coord key h.1 h.2.1]

def setStack (s : BitStore K Aux) (key : K) (bits : List Bool) : BitStore K Aux :=
  ⟨s.state, Function.update s.stk key bits⟩

theorem pack_setStack (base : α → BitStore K Aux) (counter coord key : K)
    (hcounter : key ≠ counter) (hcoord : key ≠ coord) (bits : α → List Bool)
    (a : α) (i remaining : Nat) (scratch : Option Bool) :
    pack (fun a => setStack (base a) key (bits a)) counter coord a i remaining scratch =
      setStack (pack base counter coord a i remaining scratch) key (bits a) := by
  apply Store.ext
  · rfl
  · funext j
    by_cases hj : j = key <;> simp_all [pack, working, setStack, Function.update_apply]

theorem packTuple_setStack (base : α → BitStore K Aux) (slots : List (K × K))
    (key : K) (hfresh : key ∉ ports slots) (bits : α → List Bool)
    (a : α) (values remaining : List Nat) (scratch : Option Bool) :
    packTuple (fun a => setStack (base a) key (bits a)) slots a values remaining scratch =
      setStack (packTuple base slots a values remaining scratch) key (bits a) := by
  induction slots generalizing base values remaining with
  | nil => rfl
  | cons slot slots ih =>
      rcases slot with ⟨counter, coord⟩
      have h : key ≠ counter ∧ key ≠ coord ∧ key ∉ ports slots := by simpa [ports] using hfresh
      simp only [packTuple, pack_setStack base counter coord key h.1 h.2.1]
      exact ih _ h.2.2 _ _

end Lax751879Proofs.StackTuples
