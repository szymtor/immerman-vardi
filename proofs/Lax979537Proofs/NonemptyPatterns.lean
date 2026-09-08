import Lax979537Proofs.ReadPatterns
import Lax979537Proofs.RuleExtension

namespace Lax979537Proofs.NonemptyPatterns

open Turing RuleConstants FactPatterns

variable (tm : FinTM2) (m d w : Nat)

@[reducible] def numVars := ControlRules.numVars tm m d w + (w + 1)
def base : Fin (ControlRules.numVars tm m d w) → Fin (numVars tm m d w) := Fin.castAdd (w + 1)
def xvars : Fin d → Fin (numVars tm m d w) := base tm m d w ∘ ControlRules.before m d (ControlRules.headWidth tm w)
def yvars : Fin d → Fin (numVars tm m d w) := base tm m d w ∘ ControlRules.after m d (ControlRules.headWidth tm w)
def hvars : Fin (ControlRules.headWidth tm w) → Fin (numVars tm m d w) :=
  base tm m d w ∘ ControlRules.heads m d (ControlRules.headWidth tm w)
def pvars : Fin (w + 1) → Fin (numVars tm m d w) := Fin.natAdd (ControlRules.numVars tm m d w)
def qvars : Fin m → Fin (numVars tm m d w) := base tm m d w ∘ ControlRules.query m d (ControlRules.headWidth tm w)

noncomputable def source (c : TM2Micro.Cursor tm.Γ tm.Λ tm.σ) (v : tm.σ) :
    Fin (FactCodes.payloadWidth tm d w + 1) → Fin (MachineConstants.bound tm + numVars tm m d w) :=
  RuleExtension.embed _ _ (w + 1) ∘
    ControlRules.pattern tm m d w c v (ControlRules.before m d (ControlRules.headWidth tm w))

noncomputable def output (e : ReadEffects.Effect tm) (a : tm.Γ e.key) :
    Fin (FactCodes.payloadWidth tm d w + 1) → Fin (MachineConstants.bound tm + numVars tm m d w) :=
  ReadPatterns.output tm (Fin.castAdd _ (MachineConstants.numeral tm 0))
    (Fin.castAdd _ (MachineConstants.control tm e.next))
    (Fin.castAdd _ (MachineConstants.state tm (e.state (some a)))) e.key e.pop
    (Fin.natAdd _ ∘ yvars tm m d w) (Fin.natAdd _ ∘ hvars tm m d w) (Fin.natAdd _ ∘ pvars tm m d w)

noncomputable def node (e : ReadEffects.Effect tm) (a : tm.Γ e.key) :
    Fin (FactCodes.payloadWidth tm d w + 1) → Fin (MachineConstants.bound tm + numVars tm m d w) :=
  record tm d (Fin.castAdd _ (MachineConstants.numeral tm 0)) (Fin.castAdd _ (MachineConstants.numeral tm 1))
    (HeadPatterns.get tm (Fin.natAdd _ ∘ hvars tm m d w) e.key)
    (Fin.castAdd _ (MachineConstants.symbol tm (Sigma.mk e.key a))) (Fin.natAdd _ ∘ pvars tm m d w)

variable {tm m d w} {n : Nat}

theorem assignment_source (hn : MachineConstants.bound tm ≤ n)
    (a : Fin (numVars tm m d w) → Fin n) (c : TM2Micro.Cursor tm.Γ tm.Λ tm.σ) (v : tm.σ) :
    assignment hn a ∘ source tm m d w c v =
      ControlRules.value hn c v (a ∘ xvars tm m d w) (a ∘ hvars tm m d w) := by
  rw [source, ← Function.comp_assoc, RuleExtension.assignment_embed, ControlRules.assignment_pattern]
  rfl

theorem assignment_output (hn : MachineConstants.bound tm ≤ n)
    (a : Fin (numVars tm m d w) → Fin n) (e : ReadEffects.Effect tm) (b : tm.Γ e.key) :
    assignment hn a ∘ output tm m d w e b = ReadPatterns.value hn e b
      (a ∘ yvars tm m d w) (a ∘ hvars tm m d w) (a ∘ pvars tm m d w) := by
  rw [output, ReadPatterns.map_output]
  have hd {k : Nat} (z : Fin k → Fin (numVars tm m d w)) :
      assignment hn a ∘ (Fin.natAdd _ ∘ z) = a ∘ z := by funext i; simp [assignment]
  rw [hd, hd, hd]
  simp only [assignment, Fin.append_left]
  rfl

theorem assignment_node (hn : MachineConstants.bound tm ≤ n)
    (a : Fin (numVars tm m d w) → Fin n) (e : ReadEffects.Effect tm) (b : tm.Γ e.key) :
    assignment hn a ∘ node tm m d w e b = ReadPatterns.nodeValue (d := d) hn (Sigma.mk e.key b)
      (HeadPatterns.get tm (a ∘ hvars tm m d w) e.key) (a ∘ pvars tm m d w) := by
  rw [node, map_record, HeadPatterns.map_get]
  have hd {k : Nat} (z : Fin k → Fin (numVars tm m d w)) :
      assignment hn a ∘ (Fin.natAdd _ ∘ z) = a ∘ z := by funext i; simp [assignment]
  rw [hd, hd]
  simp only [assignment, Fin.append_left]
  rfl

def data (q : Fin m → Fin n) (x y : Fin d → Fin n) (h : Fin (ControlRules.headWidth tm w) → Fin n)
    (p : Fin (w + 1) → Fin n) : Fin (numVars tm m d w) → Fin n :=
  Fin.append (ControlRules.data q x y h) p

@[simp] theorem data_x (q : Fin m → Fin n) (x y : Fin d → Fin n)
    (h : Fin (ControlRules.headWidth tm w) → Fin n) (p : Fin (w + 1) → Fin n) :
    data q x y h p ∘ xvars tm m d w = x := by
  funext i; simp [data, xvars, base, ControlRules.data, ControlRules.before]
@[simp] theorem data_y (q : Fin m → Fin n) (x y : Fin d → Fin n)
    (h : Fin (ControlRules.headWidth tm w) → Fin n) (p : Fin (w + 1) → Fin n) :
    data q x y h p ∘ yvars tm m d w = y := by
  funext i; simp [data, yvars, base, ControlRules.data, ControlRules.after]
@[simp] theorem data_h (q : Fin m → Fin n) (x y : Fin d → Fin n)
    (h : Fin (ControlRules.headWidth tm w) → Fin n) (p : Fin (w + 1) → Fin n) :
    data q x y h p ∘ hvars tm m d w = h := by
  funext i; simp [data, hvars, base, ControlRules.data, ControlRules.heads]
@[simp] theorem data_p (q : Fin m → Fin n) (x y : Fin d → Fin n)
    (h : Fin (ControlRules.headWidth tm w) → Fin n) (p : Fin (w + 1) → Fin n) :
    data q x y h p ∘ pvars tm m d w = p := by
  funext i; simp [data, pvars]
@[simp] theorem data_q (q : Fin m → Fin n) (x y : Fin d → Fin n)
    (h : Fin (ControlRules.headWidth tm w) → Fin n) (p : Fin (w + 1) → Fin n) :
    data q x y h p ∘ qvars tm m d w = q := by
  funext i; simp [data, qvars, base, ControlRules.data, ControlRules.query]

end Lax979537Proofs.NonemptyPatterns
