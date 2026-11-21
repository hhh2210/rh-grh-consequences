/-
The proof of the large-x estimate is adapted from Google LLC's Cryptids,
Cryptids/Semantics/Riemann/Analytic.lean, commit 3647718b5df22e1a61462dec0376bd204526285a,
lines 590–617. Copyright (c) 2026 Google LLC. Licensed under Apache 2.0.
Modifications: standalone imports and an explicit inequality in the statement.
-/
import PsiCompact
import PrimeCountingFromPsi
import Cryptids.Semantics.Riemann.HorizontalBounds
import Cryptids.Semantics.Riemann.WeightedStieltjes
import Cryptids.Semantics.Riemann.ExplicitLarge

open ConjectureMachines.Semantics.Riemann

namespace CarryForward.Targets

/-- Cryptids' real-valued large-x bound on ψ with its explicit threshold. -/
theorem abs_psi_sub_self_le_seven_eighths_of_five_thousand_le (hRH : RiemannHypothesis)
    {x : ℝ} (hx : 5000 ≤ x) :
    |Chebyshev.psi x - x| ≤ (7 / 8 : ℝ) * Real.sqrt x * (Real.log x) ^ 2 := by
  obtain ⟨⟨hx_sub, hh_pos, h6T⟩, h_rhs⟩ :=
    ExplicitLarge.explicit_rhs_le_seven_eighths_of_five_thousand_le hx
  obtain ⟨C_h, hCh, h_heights_hb⟩ :=
    HorizontalBounds.exists_zero_free_height_with_log_pow_five_bound hRH h6T
  have hN_bound : ∀ t ≥ 6,
      (WeightedStieltjes.weightedZeroCountingFunction t : ℝ) ≤
        (16 / 5 : ℝ) * t * Real.log t + (11 / 5 : ℝ) * t + (0 : ℝ) := by
    intro t ht
    rw [add_zero]
    exact VonMangoldtCount.weightedZeroCountingFunction_le_sixteen_fifths hRH ht
  have h_left_zeta : ∀ t : ℝ,
      ‖-deriv riemannZeta (((-1 / 4 : ℝ) : ℂ) + (t : ℂ) * Complex.I) /
        riemannZeta (((-1 / 4 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        (1 : ℝ) * Real.log (|t| + 2) + (85 : ℝ) := by
    intro t
    have h_eq : (((-1 / 4 : ℝ) : ℂ) + (t : ℂ) * Complex.I) =
        (-1 / 4 : ℂ) + (t : ℂ) * Complex.I := by push_cast; ring
    rw [h_eq, neg_div, norm_neg, ← logDeriv_apply, one_mul]
    exact DigammaBinet.norm_logDeriv_riemannZeta_leftVertical_le_eighty_five t
  have h_explicit :=
    WeightedStieltjes.abs_psi_sub_self_le_weighted_riemannVonMangoldt_six_neg_one_fourth
      hRH hx_sub hh_pos h6T (by norm_num) (by norm_num) (by norm_num) (by norm_num) hCh
      hN_bound h_left_zeta h_heights_hb
  exact h_explicit.trans h_rhs

/-- The von Koch estimate for ψ on the whole interval x ≥ 2 under RH. -/
theorem psi_bound_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ∃ C : ℝ, ∀ x ≥ 2, |Chebyshev.psi x - x| ≤ C * Real.sqrt x * Real.log x ^ 2 :=
  psi_bound_of_large_bound (X := 5000) (A := 7 / 8) fun _ hx ↦
    abs_psi_sub_self_le_seven_eighths_of_five_thousand_le hRH hx

/-- Von Koch's conditional prime-counting error estimate for all real x ≥ 2. -/
theorem primeCountingError_of_riemannHypothesis (hRH : RiemannHypothesis) : PrimeCountingError :=
  primeCountingError_of_psi_bound (psi_bound_of_riemannHypothesis hRH)

#print axioms abs_psi_sub_self_le_seven_eighths_of_five_thousand_le
#print axioms psi_bound_of_riemannHypothesis
#print axioms primeCountingError_of_riemannHypothesis

end CarryForward.Targets
