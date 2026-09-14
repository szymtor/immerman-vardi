import Lax751879.FixedPointSemantics

namespace Lax751879Proofs.SyntaxOperations

open Lax751879.OrderedStructures Lax751879.FixedPointSyntax
open Lax751879.FixedPointSemantics

def liftOne {m l : Nat} (f : Fin m → Fin l) : Fin (m + 1) → Fin (l + 1) :=
  Fin.cons 0 (fun x => (f x).succ)

def liftBlock {m l : Nat} (k : Nat) (f : Fin m → Fin l) :
    Fin (k + m) → Fin (k + l) :=
  Fin.append (Fin.castAdd l) (fun x => Fin.natAdd k (f x))

/-- Capture-avoiding renaming of the free element variables. -/
def rename {σ : Vocabulary} {m : Nat} {ρ : List Nat}
    (φ : RawFormula σ m ρ) {l : Nat} (f : Fin m → Fin l) : RawFormula σ l ρ :=
  match φ with
  | .truth => .truth
  | .equal x y => .equal (f x) (f y)
  | .less x y => .less (f x) (f y)
  | .relation r args => .relation r (f ∘ args)
  | .variable r args => .variable r (f ∘ args)
  | .neg ψ => .neg (rename ψ f)
  | .conj ψ χ => .conj (rename ψ f) (rename χ f)
  | .exists' ψ => .exists' (rename ψ (liftOne f))
  | .lfp k body args => .lfp k (rename body (liftBlock k f)) (f ∘ args)

theorem rename_positiveAt {σ : Vocabulary} {m : Nat} {ρ : List Nat}
    (φ : RawFormula σ m ρ) {l : Nat} (f : Fin m → Fin l)
    (r : Fin ρ.length) (p : Bool) :
    (rename φ f).positiveAt r p ↔ φ.positiveAt r p := by
  induction φ generalizing l p with
  | truth | equal | less | relation | «variable» => rfl
  | neg ψ ih => exact ih _ r (!p)
  | conj ψ χ ihψ ihχ => exact and_congr (ihψ _ r p) (ihχ _ r p)
  | exists' ψ ih => exact ih _ r p
  | lfp k body args ih => exact ih _ r.succ p

theorem rename_admissible {σ : Vocabulary} {m : Nat} {ρ : List Nat}
    (φ : RawFormula σ m ρ) {l : Nat} (f : Fin m → Fin l) :
    (rename φ f).Admissible ↔ φ.Admissible := by
  induction φ generalizing l with
  | truth | equal | less | relation | «variable» => rfl
  | neg ψ ih => exact ih _
  | conj ψ χ ihψ ihχ => exact and_congr (ihψ _) (ihχ _)
  | exists' ψ ih => exact ih _
  | lfp k body args ih =>
      exact and_congr (ih _) (rename_positiveAt body _ 0 true)

theorem cons_comp_liftOne {α : Type} {m l : Nat} (a : α) (v : Fin l → α)
    (f : Fin m → Fin l) :
    Fin.cons a v ∘ liftOne f = Fin.cons a (v ∘ f) := by
  funext x
  exact Fin.cases rfl (fun _ => rfl) x

theorem append_comp_liftBlock {α : Type} {m l k : Nat} (a : Fin k → α)
    (v : Fin l → α) (f : Fin m → Fin l) :
    Fin.append a v ∘ liftBlock k f = Fin.append a (v ∘ f) := by
  funext x
  refine Fin.addCases ?_ ?_ x
  · intro i
    simp [Function.comp_def, liftBlock, Fin.append]
  · intro i
    simp [Function.comp_def, liftBlock, Fin.append]

theorem eval_rename {σ : Vocabulary} {m : Nat} {ρ : List Nat}
    (φ : RawFormula σ m ρ) (A : OrderedStructure σ)
    {l : Nat} (f : Fin m → Fin l) (v : Fin l → Fin A.size)
    (η : RelationEnv A.size ρ) :
    eval (rename φ f) A v η ↔ eval φ A (v ∘ f) η := by
  induction φ generalizing l with
  | truth | equal | less | relation | «variable» => rfl
  | neg ψ ih => exact not_congr (ih f v η)
  | conj ψ χ ihψ ihχ => exact and_congr (ihψ f v η) (ihχ f v η)
  | exists' ψ ih =>
      apply exists_congr
      intro a
      simpa only [cons_comp_liftOne] using ih (liftOne f) (Fin.cons a v) η
  | lfp k body args ih =>
      have hF : (fun R => {a | eval (rename body (liftBlock k f)) A
          (Fin.append a v) (extend R η)}) =
          (fun R => {a | eval body A (Fin.append a (v ∘ f)) (extend R η)}) := by
        funext R
        apply Set.ext
        intro a
        simpa only [Set.mem_setOf_eq, append_comp_liftBlock] using
          ih (liftBlock k f) (Fin.append a v) (extend R η)
      change Lax751879.LeastFixedPoints.leastFixedPoint _ (v ∘ (f ∘ args)) ↔
        Lax751879.LeastFixedPoints.leastFixedPoint _ ((v ∘ f) ∘ args)
      rw [hF]
      rfl

end Lax751879Proofs.SyntaxOperations
