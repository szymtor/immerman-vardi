import Lax751879Proofs.FactCodes
import Lax751879Proofs.RuleConstants

namespace Lax751879Proofs.MachineConstants

open Turing

/-- One fixed numeral block contains all tags, supported machine symbols,
supported control locations, and finite internal states. -/
noncomputable def bound (tm : FinTM2) : Nat :=
  3 + ((TM2MicroSupport.controls tm).card + 1) +
    ((TM2Alphabet.alphabet tm).card + 1) + @Fintype.card tm.σ tm.σFin

theorem enough (tm : FinTM2) : 3 ≤ bound tm := by unfold bound; omega
theorem controls_bound (tm : FinTM2) : (TM2MicroSupport.controls tm).card + 1 ≤ bound tm := by
  unfold bound; omega
theorem symbols_bound (tm : FinTM2) : (TM2Alphabet.alphabet tm).card + 1 ≤ bound tm := by
  unfold bound; omega
theorem states_bound (tm : FinTM2) : @Fintype.card tm.σ tm.σFin ≤ bound tm := by
  unfold bound; omega

noncomputable def numeral (tm : FinTM2) (j : Fin 3) : Fin (bound tm) := Fin.castLE (enough tm) j
noncomputable def control (tm : FinTM2) (c : TM2Micro.Cursor tm.Γ tm.Λ tm.σ) : Fin (bound tm) :=
  SupportedCodes.code _ (controls_bound tm) c
noncomputable def symbol (tm : FinTM2) (a : Sigma tm.Γ) : Fin (bound tm) :=
  SupportedCodes.code _ (symbols_bound tm) a
noncomputable def state (tm : FinTM2) (v : tm.σ) : Fin (bound tm) :=
  @TupleCoding.finiteCode tm.σ tm.σFin _ (states_bound tm) v

theorem cast_control (tm : FinTM2) {n : Nat} (hn : bound tm ≤ n)
    (c : TM2Micro.Cursor tm.Γ tm.Λ tm.σ) :
    Fin.castLE hn (control tm c) = SupportedCodes.code _ ((controls_bound tm).trans hn) c := rfl

theorem cast_state (tm : FinTM2) {n : Nat} (hn : bound tm ≤ n) (v : tm.σ) :
    Fin.castLE hn (state tm v) =
      @TupleCoding.finiteCode tm.σ tm.σFin n ((states_bound tm).trans hn) v := rfl

theorem cast_symbol (tm : FinTM2) {n : Nat} (hn : bound tm ≤ n) (a : Sigma tm.Γ) :
    Fin.castLE hn (symbol tm a) = SupportedCodes.code _ ((symbols_bound tm).trans hn) a := rfl

end Lax751879Proofs.MachineConstants
