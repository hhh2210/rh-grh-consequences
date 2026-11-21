import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

namespace CarryForward.Targets

open Real

/-- An explicit constant on a bounded interval absorbs the small values of x in
a von Koch bound. The upper endpoint X is arbitrary. -/
theorem psi_error_on_interval {x X : ℝ} (hx : 2 ≤ x) (hxX : x ≤ X) :
    |Chebyshev.psi x - x| ≤
      (4 * (log 4 + 5) * sqrt X) * sqrt x * log x ^ 2 := by
  have hx0 : 0 ≤ x := by linarith
  have hconst : 0 ≤ log 4 + 5 := by positivity
  have hlog : 1 / 2 ≤ log x :=
    (by linarith [Real.log_two_gt_d9] : (1 : ℝ) / 2 ≤ log 2).trans
      (Real.log_le_log (by norm_num) hx)
  have hsq : 1 ≤ 4 * log x ^ 2 := by nlinarith [sq_nonneg (log x - 1 / 2)]
  have hscale : x ≤ sqrt X * sqrt x := by
    calc x = sqrt x * sqrt x := (Real.mul_self_sqrt hx0).symm
      _ ≤ sqrt X * sqrt x := mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hxX) (sqrt_nonneg x)
  have hb : |Chebyshev.psi x - x| ≤ (log 4 + 5) * x := by
    have hup := Chebyshev.psi_le_const_mul_self hx0
    have hnon := Chebyshev.psi_nonneg x
    have h₄ : 0 ≤ log 4 := by positivity
    exact abs_le.mpr ⟨by nlinarith [mul_nonneg h₄ hx0], by linarith⟩
  calc
    |Chebyshev.psi x - x| ≤ (log 4 + 5) * x := hb
    _ ≤ (log 4 + 5) * (sqrt X * sqrt x) := mul_le_mul_of_nonneg_left hscale hconst
    _ ≤ ((log 4 + 5) * (sqrt X * sqrt x)) * (4 * log x ^ 2) := by
      exact le_mul_of_one_le_right (by positivity) hsq
    _ = _ := by ring

/-- Extend a large-x estimate to every x ≥ 2 by taking the maximum of the two constants. -/
theorem psi_bound_of_large_bound {X A : ℝ}
    (h : ∀ x ≥ X, |Chebyshev.psi x - x| ≤ A * sqrt x * log x ^ 2) :
    ∃ C : ℝ, ∀ x ≥ 2, |Chebyshev.psi x - x| ≤ C * sqrt x * log x ^ 2 := by
  refine ⟨max A (4 * (log 4 + 5) * sqrt X), fun x hx ↦ ?_⟩
  by_cases hlarge : X ≤ x
  · exact (h x hlarge).trans <|
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (sqrt_nonneg x)) (sq_nonneg _)
  · exact (psi_error_on_interval hx (le_of_not_ge hlarge)).trans <|
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (sqrt_nonneg x)) (sq_nonneg _)

#print axioms psi_error_on_interval
#print axioms psi_bound_of_large_bound

end CarryForward.Targets
