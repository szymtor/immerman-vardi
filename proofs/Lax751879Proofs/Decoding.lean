import Lax751879Proofs.StructureEncoding
import Mathlib.Data.Fintype.Pi

-- Preserve Lean 4.30 elaboration of dependent indices during this port.
set_option backward.isDefEq.respectTransparency false

namespace Lax751879Proofs.Decoding

open Lax751879.OrderedStructures Lax751879.StructureEncoding

def readUnary : List Bool → Option (Nat × List Bool)
  | [] => none
  | false :: xs => some (0, xs)
  | true :: xs => do
      let (n, rest) ← readUnary xs
      pure (n + 1, rest)

theorem readUnary_correct (n : Nat) (rest : List Bool) :
    readUnary (unary n ++ rest) = some (n, rest) := by
  induction n with
  | zero => simp [unary, readUnary]
  | succ n ih =>
      simp only [unary, List.replicate_succ, List.cons_append, readUnary]
      change (readUnary (unary n ++ rest)).bind
        (fun p => some (p.1 + 1, p.2)) = _
      rw [ih]
      rfl

/-- Retrieve a bit by scanning the finite tuple enumeration. -/
def readTable {α : Type} [DecidableEq α] : List α → List Bool → α → Bool
  | t :: ts, b :: bs, a => if t = a then b else readTable ts bs a
  | _, _, _ => false

theorem readTable_correct {α : Type} [DecidableEq α] (ts : List α)
    (f : α → Bool) (a : α) (ha : a ∈ ts) :
    readTable ts (ts.map f) a = f a := by
  induction ts with
  | nil => simp at ha
  | cons t ts ih =>
      by_cases h : t = a
      · subst t
        simp [readTable]
      · have hat : a ∈ ts := (List.mem_cons.mp ha).resolve_left (Ne.symm h)
        simpa [readTable, h] using ih hat

abbrev Relations (n : Nat) (σ : Vocabulary) :=
  (r : Symbol σ) → (Fin (σ.get r) → Fin n) → Bool

def relationBits {σ : Vocabulary} (n : Nat) (R : Relations n σ) : List Bool :=
  (List.finRange σ.length).flatMap fun r => (tuples n (σ.get r)).map (R r)

def readRelations (n : Nat) : (σ : Vocabulary) → List Bool →
    Option (Relations n σ × List Bool)
  | [], w => some ((fun r => Fin.elim0 r), w)
  | k :: σ, w =>
      if n ^ k ≤ w.length then do
        let (R, rest) ← readRelations n σ (w.drop (n ^ k))
        pure (Fin.cons (readTable (tuples n k) (w.take (n ^ k))) R, rest)
      else none

theorem relationBits_cons {σ : Vocabulary} (n k : Nat) (R : Relations n (k :: σ)) :
    relationBits n R = (tuples n k).map (R 0) ++
      relationBits n (fun r => R r.succ) := by
  simp [relationBits, List.finRange_succ, List.flatMap_map]

theorem readRelations_correct (n : Nat) (σ : Vocabulary)
    (R : Relations n σ) (rest : List Bool) :
    readRelations n σ (relationBits n R ++ rest) = some (R, rest) := by
  induction σ with
  | nil =>
      have hR : R = fun r => Fin.elim0 r := by
        funext r
        exact Fin.elim0 r
      rw [hR]
      rfl
  | cons k σ ih =>
      rw [relationBits_cons, List.append_assoc]
      have hlen : ((tuples n k).map (R 0)).length = n ^ k := by
        simp [StructureEncoding.tuples_length]
      have htake : (((tuples n k).map (R 0)) ++
          (relationBits n (fun r => R r.succ) ++ rest)).take (n ^ k) =
          (tuples n k).map (R 0) := by
        rw [← hlen, List.take_left]
      have hdrop : (((tuples n k).map (R 0)) ++
          (relationBits n (fun r => R r.succ) ++ rest)).drop (n ^ k) =
          relationBits n (fun r => R r.succ) ++ rest := by
        rw [← hlen, List.drop_left]
      have hbound : n ^ k ≤ (((tuples n k).map (R 0)) ++
          (relationBits n (fun r => R r.succ) ++ rest)).length := by
        simp only [List.length_append, hlen]
        omega
      simp only [readRelations, hbound, ↓reduceIte, hdrop, ih, htake,
        Option.bind_eq_bind, Option.bind_some, pure]
      apply congrArg (fun R : Relations n (k :: σ) => some (R, rest))
      funext r
      refine Fin.cases ?_ (fun _ => rfl) r
      exact funext fun a => readTable_correct _ _ a (StructureEncoding.mem_tuples _ _ a)

def tupleBits {n k : Nat} (a : Fin k → Fin n) : List Bool :=
  (List.finRange k).flatMap fun i => unary (a i).val

def readTuple (n : Nat) : (k : Nat) → List Bool →
    Option ((Fin k → Fin n) × List Bool)
  | 0, w => some (Fin.elim0, w)
  | k + 1, w => do
      let (a, rest) ← readUnary w
      if h : a < n then do
        let (v, rest) ← readTuple n k rest
        pure (Fin.cons ⟨a, h⟩ v, rest)
      else none

theorem readTuple_correct (n k : Nat) (a : Fin k → Fin n) (rest : List Bool) :
    readTuple n k (tupleBits a ++ rest) = some (a, rest) := by
  induction k with
  | zero =>
      have ha : a = Fin.elim0 := Subsingleton.elim _ _
      simp [tupleBits, readTuple, ha]
  | succ k ih =>
      have heq : tupleBits a = unary (a 0).val ++ tupleBits (Fin.tail a) := by
        simp [tupleBits, List.finRange_succ, List.flatMap_map, Fin.tail]
      rw [heq, List.append_assoc]
      simp only [readTuple, readUnary_correct, Option.bind_eq_bind, Option.bind_some, (a 0).isLt,
        ↓reduceDIte, ih]
      change some (Fin.cons (a 0) (Fin.tail a), rest) = some (a, rest)
      rw [Fin.cons_self_tail]

/-- Parse the input and reject trailing data. -/
def decode (σ : Vocabulary) (k : Nat) (w : List Bool) :
    Option (PointedStructure σ k) := do
  let (n, rest) ← readUnary w
  let (R, rest) ← readRelations n σ rest
  let (a, rest) ← readTuple n k rest
  if rest = [] then pure ⟨⟨n, R⟩, a⟩ else none

theorem decode_encode {σ : Vocabulary} {k : Nat} (A : PointedStructure σ k) :
    decode σ k (encode A) = some A := by
  rcases A with ⟨⟨n, R⟩, a⟩
  change decode σ k ((unary n ++ relationBits n R) ++ tupleBits a) = _
  rw [List.append_assoc]
  simp only [decode, readUnary_correct, Option.bind_eq_bind, Option.bind_some, readRelations_correct]
  rw [← List.append_nil (tupleBits a), readTuple_correct]
  rfl

end Lax751879Proofs.Decoding
