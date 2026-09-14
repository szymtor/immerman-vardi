import Lax751879Proofs.NodeCodes
import Lax751879Proofs.SupportedCodes
import Lax751879Proofs.FactSupport

namespace Lax751879Proofs.FactCodes

open Turing NodeMachine NodeClosure NodeSupport FactSupport TupleCoding

variable {Initial : Type} {n iWidth d w : Nat}

/-- Proof-side interpretation data. All tuple widths depend only on the
fixed machine and chosen dimensions, never on the structure size. -/
structure Parameters (tm : FinTM2) (Initial : Type) (n iWidth d w : Nat) where
  enough : 3 ≤ n
  initial : Initial → Fin iWidth → Fin n
  initial_injective : Function.Injective initial
  initial_width : iWidth ≤ w
  clock_width : d ≤ w
  controls_bound : (TM2MicroSupport.controls tm).card + 1 ≤ n
  symbols_bound : (TM2Alphabet.alphabet tm).card + 1 ≤ n
  states_bound : @Fintype.card tm.σ tm.σFin ≤ n

@[reducible] def stackCount (tm : FinTM2) : Nat := @Fintype.card tm.K tm.kFin
@[reducible] def configWidth (tm : FinTM2) (d w : Nat) : Nat := d + (stackCount tm * (w + 1) + 2)
@[reducible] def recordWidth (w : Nat) : Nat := (w + 1) + (w + 2)
@[reducible] def payloadWidth (tm : FinTM2) (d w : Nat) : Nat := max (configWidth tm d w) (recordWidth w)

variable {tm : FinTM2} (P : Parameters tm Initial n iWidth d w)

noncomputable def heads (h : tm.K → Option (TimedNodes.Node Initial)) :
    Fin (stackCount tm * (w + 1)) → Fin n :=
  rows (@Fintype.equivFin tm.K tm.kFin) (fun k => NodeCodes.code (d := d) P.enough P.initial (h k))

theorem heads_injective {h g : tm.K → Option (TimedNodes.Node Initial)}
    (hh : ∀ k, Within (n ^ d) (h k)) (hg : ∀ k, Within (n ^ d) (g k)) (he : heads P h = heads P g) : h = g := by
  have hrows := rows_injective (@Fintype.equivFin tm.K tm.kFin) he
  funext k
  exact NodeCodes.code_injective P.enough P.initial P.initial_injective P.initial_width P.clock_width
    (hh k) (hg k) (congrFun hrows k)

noncomputable def configuration (t : Nat) (c : NodeMachine.Cfg tm.Γ tm.Λ tm.σ (TimedNodes.Node Initial)) :
    Fin (configWidth tm d w) → Fin n :=
  Fin.append (clock (d := d) (by have := P.enough; omega) t)
    (Fin.cons (SupportedCodes.code _ P.controls_bound c.cursor)
      (Fin.cons (@finiteCode tm.σ tm.σFin n P.states_bound c.var) (heads P c.heads)))

theorem configuration_injective {t s : Nat}
    {c e : NodeMachine.Cfg tm.Γ tm.Λ tm.σ (TimedNodes.Node Initial)}
    (hc : Valid tm (n ^ d) (.config t c)) (he : Valid tm (n ^ d) (.config s e))
    (h : configuration P t c = configuration P s e) : t = s ∧ c = e := by
  obtain ⟨htime, hrest⟩ := append_inj h
  have hts := clock_injective (by have := P.enough; omega : 0 < n) hc.1 he.1 htime
  obtain ⟨hcursor, hrest⟩ := Fin.cons_inj.mp hrest
  obtain ⟨hstate, hheads⟩ := Fin.cons_inj.mp hrest
  have hce := SupportedCodes.code_injective _ P.controls_bound hc.2.1 he.2.1 hcursor
  have hve := @finiteCode_injective tm.σ tm.σFin n P.states_bound _ _ hstate
  have hhe := heads_injective P hc.2.2 he.2.2 hheads
  refine ⟨hts, ?_⟩
  cases c; cases e
  cases hce; cases hve; cases hhe
  rfl

noncomputable def record (r : TimedNodes.Node Initial × Sigma tm.Γ × Option (TimedNodes.Node Initial)) :
    Fin (recordWidth w) → Fin n :=
  Fin.append (NodeCodes.code (d := d) P.enough P.initial (some r.1))
    (Fin.cons (SupportedCodes.code _ P.symbols_bound r.2.1)
      (NodeCodes.code (d := d) P.enough P.initial r.2.2))

theorem record_injective
    {r s : TimedNodes.Node Initial × Sigma tm.Γ × Option (TimedNodes.Node Initial)}
    (hr : Valid tm (n ^ d) (.node r)) (hs : Valid tm (n ^ d) (.node s))
    (he : record P r = record P s) : r = s := by
  obtain ⟨hkey, hrest⟩ := append_inj he
  obtain ⟨hsymbol, hparent⟩ := Fin.cons_inj.mp hrest
  have hk := NodeCodes.code_injective P.enough P.initial P.initial_injective P.initial_width P.clock_width
    (fun n he => by cases he; exact hr.1) (fun n he => by cases he; exact hs.1) hkey
  have ha := SupportedCodes.code_injective _ P.symbols_bound hr.2.1 hs.2.1 hsymbol
  have hp := NodeCodes.code_injective P.enough P.initial P.initial_injective P.initial_width P.clock_width
    hr.2.2 hs.2.2 hparent
  rcases r with ⟨r, a, p⟩
  rcases s with ⟨s, b, q⟩
  have hks : r = s := Option.some.inj hk
  cases hks; cases ha; cases hp
  rfl

noncomputable def code (f : Fact tm.Γ tm.Λ tm.σ Initial) : Fin (payloadWidth tm d w + 1) → Fin n :=
  match f with
  | .config t c => Fin.cons ⟨0, by have := P.enough; omega⟩
      (pad ⟨0, by have := P.enough; omega⟩ (configuration P t c))
  | .node r => Fin.cons ⟨1, by have := P.enough; omega⟩
      (pad ⟨0, by have := P.enough; omega⟩ (record P r))

/-- A fixed-arity encoding is injective on every fact in the bounded,
supported computation, including all persistent heap records. -/
theorem code_injective {f g : Fact tm.Γ tm.Λ tm.σ Initial}
    (hf : Valid tm (n ^ d) f) (hg : Valid tm (n ^ d) g) (he : code P f = code P g) : f = g := by
  cases f with
  | config t c =>
      cases g with
      | config s e =>
          have hp := (Fin.cons_inj.mp he).2
          have hc := pad_injective _ (Nat.le_max_left (configWidth tm d w) (recordWidth w)) hp
          obtain ⟨rfl, rfl⟩ := configuration_injective P hf hg hc
          rfl
      | node r =>
          have ht : (0 : Nat) = 1 := congrArg Fin.val (congrFun he 0)
          cases ht
  | node r =>
      cases g with
      | config t c =>
          have ht : (1 : Nat) = 0 := congrArg Fin.val (congrFun he 0)
          cases ht
      | node s =>
          have hp := (Fin.cons_inj.mp he).2
          have hc := pad_injective _ (Nat.le_max_right (configWidth tm d w) (recordWidth w)) hp
          exact congrArg Fact.node (record_injective P hf hg hc)

end Lax751879Proofs.FactCodes
