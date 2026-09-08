import Lax979537Proofs.NodeSupport
import Lax979537Proofs.TupleCoding

namespace Lax979537Proofs.NodeCodes

open TupleCoding

variable {Initial : Type} {n iWidth d w : Nat}

def tag : Option (TimedNodes.Node Initial) → Nat
  | none => 0
  | some (.inl _) => 1
  | some (.inr _) => 2

def payload (hn : 3 ≤ n) (initial : Initial → Fin iWidth → Fin n) :
    Option (TimedNodes.Node Initial) → Fin w → Fin n
  | none => fun _ => ⟨0, by omega⟩
  | some (.inl p) => pad ⟨0, by omega⟩ (initial p)
  | some (.inr t) => pad ⟨0, by omega⟩ (clock (d := d) (by omega) t)

/-- One tag distinguishes empty heads, initial input nodes, and time-named
push nodes. Their fixed-width payloads are padded with zero. -/
def code (hn : 3 ≤ n) (initial : Initial → Fin iWidth → Fin n)
    (p : Option (TimedNodes.Node Initial)) : Fin (w + 1) → Fin n :=
  Fin.cons ⟨tag p, by cases p with
    | none => simp only [tag]; omega
    | some p => cases p <;> simp only [tag] <;> omega⟩ (payload (d := d) hn initial p)

theorem code_zero (hn : 3 ≤ n) (initial : Initial → Fin iWidth → Fin n)
    (p : Option (TimedNodes.Node Initial)) : (code (d := d) (w := w) hn initial p 0).val = tag p := rfl

theorem initial_get (hn : 3 ≤ n) (initial : Initial → Fin iWidth → Fin n)
    (hi : iWidth ≤ w) (p : Initial) (j : Fin iWidth) :
    code (d := d) hn initial (some (.inl p)) (Fin.castLE hi j).succ = initial p j := by
  simp only [code, Fin.cons_succ, payload, pad_get]

theorem time_get (hn : 3 ≤ n) (initial : Initial → Fin iWidth → Fin n)
    (hd : d ≤ w) (t : Nat) (j : Fin d) :
    code (d := d) hn initial (some (.inr t)) (Fin.castLE hd j).succ = clock (by omega : 0 < n) t j := by
  simp only [code, Fin.cons_succ, payload, pad_get]

/-- The raw clock coding is injective on exactly the bounded references
supplied by the canonical-run invariant; no claim is made for unbounded times. -/
theorem code_injective (hn : 3 ≤ n) (initial : Initial → Fin iWidth → Fin n)
    (hinj : Function.Injective initial) (hi : iWidth ≤ w) (hd : d ≤ w)
    {p q : Option (TimedNodes.Node Initial)}
    (hp : NodeSupport.Within (n ^ d) p) (hq : NodeSupport.Within (n ^ d) q)
    (he : code (w := w) (d := d) hn initial p = code (d := d) hn initial q) : p = q := by
  have ht : tag p = tag q := congrArg Fin.val (congrFun he 0)
  cases p with
  | none =>
      cases q with
      | none => rfl
      | some q => cases q <;> cases ht
  | some p =>
      cases q with
      | none => cases p <;> cases ht
      | some q =>
          cases p with
          | inl p =>
              cases q with
              | inl q =>
                  have hval : initial p = initial q := by
                    funext j
                    simpa only [initial_get] using congrFun he (Fin.castLE hi j).succ
                  have hpq := hinj hval
                  subst q; rfl
              | inr q => cases ht
          | inr p =>
              cases q with
              | inl q => cases ht
              | inr q =>
                  have hval : clock (d := d) (by omega : 0 < n) p = clock (by omega : 0 < n) q := by
                    funext j
                    simpa only [time_get] using congrFun he (Fin.castLE hd j).succ
                  have hpq := clock_injective (by omega : 0 < n) (hp _ rfl) (hq _ rfl) hval
                  subst q; rfl

end Lax979537Proofs.NodeCodes
