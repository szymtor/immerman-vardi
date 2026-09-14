import Lax751879Proofs.FiniteDecoder
import Lax751879Proofs.RawDecoding

namespace Lax751879Proofs.DecoderAgreement

open StackProgram StackTransfer StackReadRelations

def observe {α : Type} (valid : Bool) (a : α) : Option α := if valid then some a else none

theorem observe_map {α β : Type} (f : α → β) (valid : Bool) (a : α) :
    (observe valid a).map f = observe valid (f a) := by cases valid <;> rfl

variable {K Aux : Type} [DecidableEq K]

def tableData (tables : List (Nat × K)) (s : BitStore K (Aux × Bool)) : List (List Bool) :=
  tables.map (fun r => s.stk r.2)

theorem tables_agree (w : Workspace K) (n : Nat) (tables : List (Nat × K))
    (hn : (tables.map Prod.snd).Nodup) (hf : ∀ r ∈ tables, Fresh w r.2)
    (s : BitStore K (Aux × Bool)) :
    let t := StackReadRelations.result w n tables s
    observe t.state.1.2 (tableData tables t, t.stk w.input) =
      if s.state.1.2 then RawDecoding.readTables n (tables.map Prod.fst) (s.stk w.input) else none := by
  induction tables generalizing s with
  | nil => rfl
  | cons r rest ih =>
      obtain ⟨arity, table⟩ := r
      obtain ⟨hnot, hn'⟩ := List.nodup_cons.mp hn
      have hf' : ∀ r ∈ rest, Fresh w r.2 := fun r hm => hf r (by simp [hm])
      have hti : table ≠ w.input := by
        have h := (hf (arity, table) (by simp)).1
        simp only [List.mem_cons, List.not_mem_nil, not_false_eq_true, not_or, and_true] at h
        tauto
      let u := StackReadTable.result w.input table n arity s
      let t := StackReadRelations.result w n rest u
      have hkeep : t.stk table = u.stk table := by
        apply StackReadRelations.result_preserves w n rest table hti
        intro r hr he
        apply hnot
        exact List.mem_map.mpr ⟨r, hr, he.symm⟩
      have h := congrArg (Option.map (fun p : List (List Bool) × List Bool =>
        (u.stk table :: p.1, p.2))) (ih hn' hf' u)
      rw [observe_map] at h
      change observe t.state.1.2 (t.stk table :: tableData rest t, t.stk w.input) = _
      rw [hkeep, h]
      have hui : u.stk w.input = (s.stk w.input).drop (n ^ arity) := by
        simp [u, StackReadTable.result, Ne.symm hti]
      have hut : u.stk table = StackTake.paddedPrefix (n ^ arity) (s.stk w.input) := by
        simp [u, StackReadTable.result]
      rw [hui, hut]
      change (if s.state.1.2 && decide (n ^ arity ≤ (s.stk w.input).length) then
        RawDecoding.readTables n (rest.map Prod.fst) ((s.stk w.input).drop (n ^ arity)) else none).map
        (fun p => (StackTake.paddedPrefix (n ^ arity) (s.stk w.input) :: p.1, p.2)) = _
      cases s.state.1.2 with
      | false => simp
      | true =>
          by_cases hb : n ^ arity ≤ (s.stk w.input).length
          · simp only [Bool.true_and, hb, decide_true, if_true,
              List.map_cons, RawDecoding.readTables, StackTake.prefix_eq_take _ _ hb]
            cases RawDecoding.readTables n (List.map Prod.fst rest) ((s.stk w.input).drop (n ^ arity)) <;> rfl
          · simp [hb, RawDecoding.readTables]

def coordData (coords : List K) (s : BitStore K ((Aux × Bool) × Bool)) : List Nat :=
  coords.map (fun c => (s.stk c).length)

theorem coords_agree (w : Workspace K) (n : Nat) (coords : List K)
    (hn : coords.Nodup) (hf : ∀ c ∈ coords, Fresh w c)
    (s : BitStore K ((Aux × Bool) × Bool)) (hs : Ready w n s)
    (he : ∀ c ∈ coords, s.stk c = []) :
    let t := StackReadCoordinates.result w coords s
    observe t.state.1.2 (coordData coords t, t.stk w.input) =
      if s.state.1.2 then RawDecoding.readCoords n coords.length (s.stk w.input) else none := by
  induction coords generalizing s with
  | nil => rfl
  | cons c cs ih =>
      obtain ⟨hnot, hn'⟩ := List.nodup_cons.mp hn
      have hfc := hf c (by simp)
      have hci : c ≠ w.input := by
        have h := hfc.1
        simp only [List.mem_cons, List.not_mem_nil, not_false_eq_true, not_or, and_true] at h
        tauto
      have hdi : w.domain ≠ w.input := by
        have h := w.separate
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true,
          not_or, and_true] at h
        tauto
      have hdc : w.domain ≠ c := by
        have h := hfc.1
        simp only [List.mem_cons, List.not_mem_nil, not_false_eq_true, not_or, and_true] at h
        tauto
      let u := StackCoordinate.result w.input c w.domain s
      let t := StackReadCoordinates.result w cs u
      have hkeep : t.stk c = u.stk c :=
        StackReadCoordinates.result_preserves w cs c hci hnot u
      have hu : Ready w n u := StackReadCoordinates.coordinate_ready w c hfc n s hs
      have hue : ∀ d ∈ cs, u.stk d = [] := by
        intro d hm
        have hfd := (hf d (by simp [hm])).1
        simp only [List.mem_cons, List.not_mem_nil, not_false_eq_true, not_or, and_true] at hfd
        have hne : d ≠ c := fun heq => hnot (heq ▸ hm)
        rw [StackCoordinate.result_preserves w.input c w.domain d (by tauto) hne]
        exact he d (by simp [hm])
      have h := congrArg (Option.map (fun p : List Nat × List Bool => ((u.stk c).length :: p.1, p.2)))
        (ih hn' (fun d hm => hf d (by simp [hm])) u hu hue)
      rw [observe_map] at h
      change observe t.state.1.2 ((t.stk c).length :: coordData cs t, t.stk w.input) = _
      rw [hkeep, h]
      have huc : (u.stk c).length = (StackUnary.splitUnary (s.stk w.input)).1 := by
        simp [u, StackCoordinate.result, StackCheckBound.result, StackCheckedUnary.result, he c (by simp)]
      have hui : u.stk w.input = (StackUnary.splitUnary (s.stk w.input)).2.getD [] := by
        simp [u, StackCoordinate.result, StackCheckBound.result, StackCheckedUnary.result, Ne.symm hci]
      have huv : u.state.1.2 = (s.state.1.2 && (StackUnary.splitUnary (s.stk w.input)).2.isSome &&
          decide ((StackUnary.splitUnary (s.stk w.input)).1 < n)) := by
        simpa [hs.1] using StackCoordinate.result_valid w.input c w.domain hdi hdc s (he c (by simp))
      rw [huc, hui, huv]
      cases hv : s.state.1.2 with
      | false => simp
      | true =>
          rw [List.length_cons, RawDecoding.readCoords, StackUnary.splitUnary_correct]
          cases hr : (StackUnary.splitUnary (s.stk w.input)).2 with
          | none => simp
          | some rest =>
              by_cases hb : (StackUnary.splitUnary (s.stk w.input)).1 < n
              · simp only [Option.isSome_some, Bool.true_and, hb, decide_true, if_true,
                  Option.getD_some, Option.map_some, Option.bind_eq_bind, Option.bind_some]
                cases RawDecoding.readCoords n cs.length rest <;> rfl
              · simp [hb]

def stackView (l : StackDecoder.Layout K) (s : BitStore K ((Aux × Bool) × Bool)) : RawDecoding.Data :=
  ⟨(s.stk l.work.domain).length, tableData l.tables s, coordData l.coords s⟩

def finishData (n : Nat) (ts : List (List Bool)) (p : List Nat × List Bool) : Option RawDecoding.Data :=
  if p.2 = [] then some ⟨n, ts, p.1⟩ else none

/-- All phases agree with the data-level parser on every input. Earlier
failure remains failure, and later phases preserve all previously parsed data. -/
theorem decode_agree (l : StackDecoder.Layout K) (s : BitStore K ((Aux × Bool) × Bool))
    (hs : ∀ key, key ≠ l.work.input → s.stk key = []) (hv : s.state.1.2 = true) :
    let t := StackDecoder.result l s
    observe t.state.1.2 (stackView l t) =
      RawDecoding.decode (l.tables.map Prod.fst) l.coords.length (s.stk l.work.input) := by
  let n := (StackUnary.splitUnary (s.stk l.work.input)).1
  let u := StackCheckedUnary.result l.work.input l.work.domain s
  let v := StackReadRelations.result l.work n l.tables u
  let q := StackReadCoordinates.result l.work l.coords v
  have hcore := l.work.separate
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true,
    not_or, and_true] at hcore
  have hdi : l.work.domain ≠ l.work.input := by tauto
  have hu : Ready l.work n u := StackDecoder.header_ready l.work s hs
  have hvr : Ready l.work n v := StackReadRelations.tables_ready l.work n l.tables l.table_fresh u hu
  have hce : ∀ c ∈ l.coords, v.stk c = [] := by
    intro c hm
    have hcf := (l.coord_fresh c hm).1
    simp only [List.mem_cons, List.not_mem_nil, not_false_eq_true, not_or, and_true] at hcf
    rw [StackReadRelations.result_preserves l.work n l.tables c (by tauto) (l.disjoint c hm)]
    exact StackDecoder.header_fresh l.work c (l.coord_fresh c hm) s hs
  have hdn : l.work.domain ∉ l.coords := by
    intro hm
    have h := (l.coord_fresh l.work.domain hm).1
    simp at h
  have hqd : (q.stk l.work.domain).length = n := by
    rw [StackReadCoordinates.result_preserves l.work l.coords l.work.domain hdi hdn,
      hvr.1, List.length_replicate]
  have hqt : tableData l.tables q = tableData l.tables v := by
    apply List.map_congr_left
    intro r hr
    have hfr := (l.table_fresh r hr).1
    simp only [List.mem_cons, List.not_mem_nil, not_false_eq_true, not_or, and_true] at hfr
    have hnot : r.2 ∉ l.coords := by
      intro hm
      exact l.disjoint r.2 hm r hr rfl
    exact StackReadCoordinates.result_preserves l.work l.coords r.2 (by tauto) hnot v
  have htables := tables_agree l.work n l.tables l.table_keys l.table_fresh u
  change observe v.state.1.2 (tableData l.tables v, v.stk l.work.input) = _ at htables
  have hcoords := coords_agree l.work n l.coords l.coord_keys l.coord_fresh v hvr hce
  change observe q.state.1.2 (coordData l.coords q, q.stk l.work.input) = _ at hcoords
  have hend : observe (StackDecoder.finish l.work.input q).state.1.2
      (stackView l (StackDecoder.finish l.work.input q)) =
      (observe q.state.1.2 (coordData l.coords q, q.stk l.work.input)).bind
        (finishData n (tableData l.tables v)) := by
    change observe (q.state.1.2 && decide (q.stk l.work.input = []))
      (⟨(q.stk l.work.domain).length, tableData l.tables q, coordData l.coords q⟩ : RawDecoding.Data) = _
    rw [hqd, hqt]
    cases q.state.1.2 <;> by_cases he : q.stk l.work.input = [] <;> simp [observe, finishData, he]
  change observe (StackDecoder.finish l.work.input q).state.1.2
    (stackView l (StackDecoder.finish l.work.input q)) = _
  rw [hend, hcoords]
  have hbind : (if v.state.1.2 then RawDecoding.readCoords n l.coords.length (v.stk l.work.input) else none).bind
      (finishData n (tableData l.tables v)) =
      (observe v.state.1.2 (tableData l.tables v, v.stk l.work.input)).bind
        (fun p => (RawDecoding.readCoords n l.coords.length p.2).bind (finishData n p.1)) := by
    cases v.state.1.2 <;> rfl
  rw [hbind, htables]
  have huv : u.state.1.2 = (StackUnary.splitUnary (s.stk l.work.input)).2.isSome := by
    simp [u, StackCheckedUnary.result, hv]
  have hui : u.stk l.work.input = (StackUnary.splitUnary (s.stk l.work.input)).2.getD [] := by
    simp [u, StackCheckedUnary.result, Ne.symm hdi]
  rw [huv, hui, RawDecoding.decode, StackUnary.splitUnary_correct]
  cases hr : (StackUnary.splitUnary (s.stk l.work.input)).2 with
  | none => simp
  | some rest =>
      simp only [Option.isSome_some, if_true, Option.getD_some, Option.map_some,
        Option.bind_eq_bind, Option.bind_some]
      rfl

theorem finite_agree (σ : Lax751879.OrderedStructures.Vocabulary) (k : Nat) (xs : List Bool) :
    let l := FiniteDecoder.layout σ k
    let t := StackDecoder.result l (FiniteDecoder.inputStore σ k xs)
    observe t.state.1.2 (stackView l t) = (Decoding.decode σ k xs).map RawDecoding.view := by
  have h := decode_agree (FiniteDecoder.layout σ k) (FiniteDecoder.inputStore σ k xs)
    (fun p hp => by
      change p ≠ (FiniteDecoder.work σ k).input at hp
      simp [FiniteDecoder.inputStore, ioStore, hp]) rfl
  have hσ : ((FiniteDecoder.layout σ k).tables.map Prod.fst) = σ := by
    simp only [FiniteDecoder.layout, FiniteDecoder.tables, List.map_map, Function.comp_def]
    exact List.map_get_finRange σ
  have hk : (FiniteDecoder.layout σ k).coords.length = k := by
    simp [FiniteDecoder.layout, FiniteDecoder.coords]
  have hx : (FiniteDecoder.inputStore σ k xs).stk (FiniteDecoder.layout σ k).work.input = xs := by
    simp [FiniteDecoder.inputStore, ioStore, FiniteDecoder.layout]
  rw [hσ, hk, hx, RawDecoding.decode_eq] at h
  exact h

theorem observe_isSome {α : Type} (b : Bool) (a : α) : (observe b a).isSome = b := by
  cases b <;> rfl

theorem finite_validity (σ : Lax751879.OrderedStructures.Vocabulary) (k : Nat) (xs : List Bool) :
    (StackDecoder.result (FiniteDecoder.layout σ k) (FiniteDecoder.inputStore σ k xs)).state.1.2 =
      (Decoding.decode σ k xs).isSome := by
  have h := congrArg Option.isSome (finite_agree σ k xs)
  simpa only [observe_isSome, Option.isSome_map] using h

/-- The concrete decoder accepts exactly the canonical encodings of pointed
ordered structures, including the empty-domain and nullary cases. -/
theorem accepts_iff_encoding (σ : Lax751879.OrderedStructures.Vocabulary) (k : Nat) (xs : List Bool) :
    (StackDecoder.result (FiniteDecoder.layout σ k) (FiniteDecoder.inputStore σ k xs)).state.1.2 = true ↔
      ∃ A : Lax751879.OrderedStructures.PointedStructure σ k, Lax751879.StructureEncoding.encode A = xs := by
  rw [finite_validity]
  constructor
  · intro h
    cases hd : Decoding.decode σ k xs with
    | none => simp [hd] at h
    | some A => exact ⟨A, DecoderSoundness.decode_sound σ k xs A hd⟩
  · rintro ⟨A, rfl⟩
    simp [Decoding.decode_encode]

theorem finite_data (σ : Lax751879.OrderedStructures.Vocabulary) (k : Nat) (xs : List Bool)
    (A : Lax751879.OrderedStructures.PointedStructure σ k) (hd : Decoding.decode σ k xs = some A) :
    stackView (FiniteDecoder.layout σ k)
      (StackDecoder.result (FiniteDecoder.layout σ k) (FiniteDecoder.inputStore σ k xs)) = RawDecoding.view A := by
  have h := finite_agree σ k xs
  have hv := finite_validity σ k xs
  simp only [hd, Option.isSome_some] at hv
  simpa [hd, observe, hv] using h

end Lax751879Proofs.DecoderAgreement
