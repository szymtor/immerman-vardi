import Lax979537Proofs.NodeMachine

namespace Lax979537Proofs.ReadEffects

open Turing

structure Effect (tm : FinTM2) where
  key : tm.K
  state : Option (tm.Γ key) → tm.σ
  next : TM2Micro.Cursor tm.Γ tm.Λ tm.σ
  pop : Bool

def target (tm : FinTM2) (c : TM2Micro.Cursor tm.Γ tm.Λ tm.σ) (v : tm.σ) : Option (Effect tm) :=
  match c with
  | .instruction (.pop k f q) => some ⟨k, f v, .instruction q, true⟩
  | .instruction (.peek k f q) => some ⟨k, f v, .instruction q, false⟩
  | _ => none

def nextHeads {tm : FinTM2} {Node : Type} (e : Effect tm)
    (heads : tm.K → Option Node) (parent : Option Node) : tm.K → Option Node :=
  if e.pop then Function.update heads e.key parent else heads

theorem target_step (tm : FinTM2) {Node : Type} (fresh : Node)
    (H : NodeMachine.Records Node tm.Γ) (heads : tm.K → Option Node)
    {c : TM2Micro.Cursor tm.Γ tm.Λ tm.σ} {v : tm.σ} {e : Effect tm}
    (ht : target tm c v = some e) (a : Option (tm.Γ e.key)) (parent : Option Node)
    (hr : PersistentStack.Read H (heads e.key) (a.map (Sigma.mk e.key)) parent) :
    NodeMachine.Step tm.m fresh H ⟨c, v, heads⟩ H ⟨e.next, e.state a, nextHeads e heads parent⟩ := by
  cases c with
  | boundary l => cases ht
  | instruction q =>
      cases q with
      | pop k f q => cases ht; exact .pop H k f q v heads a parent hr
      | peek k f q => cases ht; exact .peek H k f q v heads a parent hr
      | push | load | branch | goto | halt => cases ht

theorem empty_step (tm : FinTM2) {Node : Type} (fresh : Node)
    (H : NodeMachine.Records Node tm.Γ) (heads : tm.K → Option Node)
    {c : TM2Micro.Cursor tm.Γ tm.Λ tm.σ} {v : tm.σ} {e : Effect tm}
    (ht : target tm c v = some e) (hempty : heads e.key = none) :
    NodeMachine.Step tm.m fresh H ⟨c, v, heads⟩ H ⟨e.next, e.state none, heads⟩ := by
  have hs := target_step tm fresh H heads ht none none (Or.inl ⟨hempty, rfl, rfl⟩)
  have he : nextHeads e heads none = heads := by
    unfold nextHeads
    split
    · rw [← hempty, Function.update_eq_self]
    · rfl
  rwa [he] at hs

end Lax979537Proofs.ReadEffects
