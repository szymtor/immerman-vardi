import Lax751879Proofs.DecoderSoundness

-- Preserve Lean 4.30 elaboration of dependent indices during this port.
set_option backward.isDefEq.respectTransparency false

namespace Lax751879Proofs.RawDecoding

open Lax751879.OrderedStructures Lax751879.StructureEncoding

/-- A proof-only observation of decoded data, with no dependent universe
indices. This matches the payload retained by the concrete stack decoder. -/
structure Data where
  size : Nat
  tables : List (List Bool)
  coords : List Nat
  deriving DecidableEq

def tableView {σ : Vocabulary} (n : Nat) (R : Decoding.Relations n σ) : List (List Bool) :=
  (List.finRange σ.length).map (fun r => (tuples n (σ.get r)).map (R r))

def coordView {n k : Nat} (v : Fin k → Fin n) : List Nat :=
  (List.finRange k).map (fun i => (v i).val)

def view {σ : Vocabulary} {k : Nat} (A : PointedStructure σ k) : Data :=
  ⟨A.structureValue.size, tableView A.structureValue.size A.structureValue.relation, coordView A.tuple⟩

def readTables (n : Nat) : List Nat → List Bool → Option (List (List Bool) × List Bool)
  | [], xs => some ([], xs)
  | k :: σ, xs => if n ^ k ≤ xs.length then do
      let (ts, rest) ← readTables n σ (xs.drop (n ^ k))
      pure (xs.take (n ^ k) :: ts, rest)
    else none

def readCoords (n : Nat) : Nat → List Bool → Option (List Nat × List Bool)
  | 0, xs => some ([], xs)
  | k + 1, xs => do
      let (a, rest) ← Decoding.readUnary xs
      if a < n then do
        let (v, rest) ← readCoords n k rest
        pure (a :: v, rest)
      else none

def decode (σ : Vocabulary) (k : Nat) (xs : List Bool) : Option Data := do
  let (n, rest) ← Decoding.readUnary xs
  let (ts, rest) ← readTables n σ rest
  let (vs, rest) ← readCoords n k rest
  if rest = [] then pure ⟨n, ts, vs⟩ else none

theorem tableView_cons (n k : Nat) (σ : Vocabulary) (R : Decoding.Relations n (k :: σ)) :
    tableView n R = (tuples n k).map (R 0) :: tableView n (fun r => R r.succ) := by
  simp [tableView, List.finRange_succ, List.map_map]

theorem coordView_cons {n k : Nat} (a : Fin n) (v : Fin k → Fin n) :
    coordView (Fin.cons a v) = a.val :: coordView v := by
  simp [coordView, List.finRange_succ, List.map_map]

theorem readTables_eq (n : Nat) (σ : Vocabulary) (xs : List Bool) :
    readTables n σ xs = (Decoding.readRelations n σ xs).map (fun p => (tableView n p.1, p.2)) := by
  induction σ generalizing xs with
  | nil => rfl
  | cons k σ ih =>
      rw [readTables, Decoding.readRelations]
      by_cases hb : n ^ k ≤ xs.length
      · simp only [hb, if_true, ih]
        cases hr : Decoding.readRelations n σ (xs.drop (n ^ k)) with
        | none => rfl
        | some p =>
            obtain ⟨R, rest⟩ := p
            simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some, pure,
              tableView_cons, Fin.cons_zero, Fin.cons_succ]
            change some (xs.take (n ^ k) :: tableView n R, rest) =
              some ((tuples n k).map (Decoding.readTable (tuples n k) (xs.take (n ^ k))) ::
                tableView n R, rest)
            rw [DecoderSoundness.readTable_map _ _ (DecoderSoundness.tuples_nodup n k)
              (by simp [StructureEncoding.tuples_length, Nat.min_eq_left hb])]
      · simp [hb]

theorem readCoords_eq (n k : Nat) (xs : List Bool) :
    readCoords n k xs = (Decoding.readTuple n k xs).map (fun p => (coordView p.1, p.2)) := by
  induction k generalizing xs with
  | zero => rfl
  | succ k ih =>
      rw [readCoords, Decoding.readTuple]
      cases hu : Decoding.readUnary xs with
      | none => rfl
      | some p =>
          obtain ⟨a, rest⟩ := p
          simp only [Option.bind_eq_bind, Option.bind_some]
          by_cases ha : a < n
          · simp only [ha, if_true, dif_pos, ih]
            cases hv : Decoding.readTuple n k rest with
            | none => rfl
            | some p =>
                obtain ⟨v, rest'⟩ := p
                simp [coordView_cons]
          · simp [ha]

/-- The unindexed observation is exactly the approved semantic decoder's
payload. It introduces no alternative acceptance criterion. -/
theorem decode_eq (σ : Vocabulary) (k : Nat) (xs : List Bool) :
    decode σ k xs = (Decoding.decode σ k xs).map view := by
  rw [decode, Decoding.decode]
  cases hu : Decoding.readUnary xs with
  | none => rfl
  | some p =>
      obtain ⟨n, ys⟩ := p
      simp only [Option.bind_eq_bind, Option.bind_some, readTables_eq]
      cases hr : Decoding.readRelations n σ ys with
      | none => rfl
      | some p =>
          obtain ⟨R, zs⟩ := p
          simp only [Option.map_some, Option.bind_some, readCoords_eq]
          cases hv : Decoding.readTuple n k zs with
          | none => rfl
          | some p =>
              obtain ⟨v, rest⟩ := p
              simp only [Option.map_some, Option.bind_some]
              by_cases he : rest = [] <;> simp [he, view]

end Lax751879Proofs.RawDecoding
