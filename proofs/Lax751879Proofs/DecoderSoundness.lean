import Lax751879Proofs.DecisionProcedure
import Mathlib.Data.Finset.Card

namespace Lax751879Proofs.DecoderSoundness

open Lax751879.OrderedStructures Lax751879.StructureEncoding Decoding

theorem readUnary_sound (w : List Bool) (n : Nat) (rest : List Bool)
    (h : readUnary w = some (n, rest)) : w = unary n ++ rest := by
  induction w generalizing n rest with
  | nil => simp [readUnary] at h
  | cons b xs ih =>
      cases b with
      | false =>
          simp only [readUnary, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rfl
      | true =>
          cases hr : readUnary xs with
          | none => simp [readUnary, hr] at h
          | some r =>
              obtain ⟨m, ys⟩ := r
              simp only [readUnary, hr, Option.bind_eq_bind, Option.bind_some, pure, Option.some.injEq,
                Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              rw [ih m ys hr]
              simp [unary, List.replicate_succ, List.append_assoc]

theorem tuples_nodup (n k : Nat) : (tuples n k).Nodup := by
  have hu : (tuples n k).toFinset = Finset.univ := by
    ext a
    simp [StructureEncoding.mem_tuples]
  have hc : (tuples n k).toFinset.card = (tuples n k).length := by
    rw [hu, StructureEncoding.tuples_length]
    simp
  exact (Multiset.toFinset_card_eq_card_iff_nodup (m := ⟦tuples n k⟧)).mp hc

theorem readTable_map {α : Type} [DecidableEq α] (ts : List α) (bs : List Bool)
    (hn : ts.Nodup) (hl : bs.length = ts.length) : ts.map (readTable ts bs) = bs := by
  induction ts generalizing bs with
  | nil => have hb : bs = [] := List.length_eq_zero_iff.mp hl; subst bs; rfl
  | cons t ts ih =>
      obtain ⟨hnt, hn'⟩ := List.nodup_cons.mp hn
      cases bs with
      | nil => simp at hl
      | cons b bs =>
          simp only [List.map_cons]
          apply congrArg₂ List.cons
          · simp [readTable]
          · have he : ts.map (readTable (t :: ts) (b :: bs)) = ts.map (readTable ts bs) := by
              apply List.map_congr_left
              intro x hx
              have htx : t ≠ x := fun h => hnt (h ▸ hx)
              simp [readTable, htx]
            rw [he]
            exact ih bs hn' (by simpa using hl)

theorem readRelations_sound (n : Nat) (σ : Vocabulary) (w : List Bool)
    (R : Relations n σ) (rest : List Bool) (h : readRelations n σ w = some (R, rest)) :
    relationBits n R ++ rest = w := by
  induction σ generalizing w rest with
  | nil =>
      simp only [readRelations, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [relationBits]
  | cons k σ ih =>
      rw [readRelations] at h
      split at h
      next hb =>
        cases hr : readRelations n σ (w.drop (n ^ k)) with
        | none => simp [hr] at h
        | some p =>
            obtain ⟨R', rest'⟩ := p
            simp only [hr, Option.bind_eq_bind, Option.bind_some, pure, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            rw [relationBits_cons]
            simp only [Fin.cons_zero, Fin.cons_succ]
            change ((tuples n k).map (readTable (tuples n k) (w.take (n ^ k))) ++
              relationBits n R') ++ rest' = w
            have hm : (tuples n k).map (readTable (tuples n k) (w.take (n ^ k))) = w.take (n ^ k) :=
              readTable_map _ _ (tuples_nodup n k) (by
                simp [StructureEncoding.tuples_length, Nat.min_eq_left hb])
            rw [hm, List.append_assoc, ih _ R' rest' hr, List.take_append_drop]
      next hb => simp at h

theorem readTuple_sound (n k : Nat) (w : List Bool) (v : Fin k → Fin n) (rest : List Bool)
    (h : readTuple n k w = some (v, rest)) : tupleBits v ++ rest = w := by
  induction k generalizing w rest with
  | zero =>
      simp only [readTuple, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [tupleBits]
  | succ k ih =>
      rw [readTuple] at h
      cases hu : readUnary w with
      | none => simp [hu] at h
      | some p =>
          obtain ⟨a, xs⟩ := p
          simp only [hu, Option.bind_eq_bind, Option.bind_some] at h
          split at h
          next ha =>
            cases hv : readTuple n k xs with
            | none => simp [hv] at h
            | some p =>
                obtain ⟨v', ys⟩ := p
                simp only [hv, Option.bind_some, pure, Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                have he : tupleBits (Fin.cons (⟨a, ha⟩ : Fin n) v') = unary a ++ tupleBits v' := by
                  simp [tupleBits, List.finRange_succ, List.flatMap_map]
                rw [he, List.append_assoc, ih _ v' ys hv, ← readUnary_sound w a xs hu]
          next ha => simp at h

theorem decode_sound (σ : Vocabulary) (k : Nat) (w : List Bool) (A : PointedStructure σ k)
    (h : decode σ k w = some A) : encode A = w := by
  rw [decode] at h
  cases hu : readUnary w with
  | none => simp [hu] at h
  | some p =>
      obtain ⟨n, xs⟩ := p
      simp only [hu, Option.bind_eq_bind, Option.bind_some] at h
      cases hr : readRelations n σ xs with
      | none => simp [hr] at h
      | some p =>
          obtain ⟨R, ys⟩ := p
          simp only [hr, Option.bind_some] at h
          cases hv : readTuple n k ys with
          | none => simp [hv] at h
          | some p =>
              obtain ⟨v, zs⟩ := p
              simp only [hv, Option.bind_some] at h
              split at h
              next hz =>
                subst zs
                simp only [pure, Option.some.injEq] at h
                subst A
                change (unary n ++ relationBits n R) ++ tupleBits v = w
                have ht := readTuple_sound n k ys v [] hv
                simp only [List.append_nil] at ht
                rw [List.append_assoc, ht, readRelations_sound n σ xs R ys hr,
                  ← readUnary_sound w n xs hu]
              next hz => simp at h

/-- The semantic parser itself already enforces canonical encodings, so a
machine implementation need not perform a second serialization pass. -/
theorem checkedDecode_eq_decode (σ : Vocabulary) (k : Nat) (w : List Bool) :
    DecisionProcedure.checkedDecode σ k w = decode σ k w := by
  cases h : decode σ k w with
  | none => simp [DecisionProcedure.checkedDecode, h]
  | some A => simp [DecisionProcedure.checkedDecode, h, decode_sound σ k w A h]

end Lax751879Proofs.DecoderSoundness
