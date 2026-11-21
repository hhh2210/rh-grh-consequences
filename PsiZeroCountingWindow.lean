import Cryptids.Semantics.Riemann.VonMangoldtCount

open Finset Filter Asymptotics Complex
open ConjectureMachines.Semantics.Riemann.VonMangoldtCount

namespace CarryForward.Targets

/-- Counts both signs of the height and counts zeros with their analytic multiplicities. -/
theorem weightedZeroCounting_unitWindow_le (hRH : RiemannHypothesis)
    {T : ℝ} (hT : 8 ≤ T) :
    (weightedZeroCountingFunction (T+1) : ℝ) - weightedZeroCountingFunction T ≤
      (512/41 : ℝ) * Real.log (T+4) := by
  classical
  let w := analyticOrderNatAt riemannZeta
  let U := nontrivialZetaZerosUpTo T
  let P := nontrivialZetaZerosInFourWindow T
  let M := nontrivialZetaZerosInFourWindow (-T)
  have hs : nontrivialZetaZerosUpTo (T+1) ⊆ U ∪ (P ∪ M) := by
    intro ρ hρ
    obtain ⟨hz, hh⟩ := mem_nontrivialZetaZerosUpTo.mp hρ
    by_cases hlo : |ρ.im| ≤ T
    · exact mem_union_left _ (mem_nontrivialZetaZerosUpTo.mpr ⟨hz, hlo⟩)
    · apply mem_union_right
      replace hlo := lt_of_not_ge hlo
      rcases le_or_gt 0 ρ.im with hp | hm
      · rw [abs_of_nonneg hp] at hlo hh
        exact mem_union_left _ (mem_nontrivialZetaZerosInFourWindow.mpr ⟨hz, by linarith, by linarith⟩)
      · rw [abs_of_neg hm] at hlo hh
        exact mem_union_right _ (mem_nontrivialZetaZerosInFourWindow.mpr ⟨hz, by linarith, by linarith⟩)
  have hn : weightedZeroCountingFunction (T+1) ≤
      weightedZeroCountingFunction T + (∑ ρ ∈ P, w ρ) + ∑ ρ ∈ M, w ρ := by
    change ∑ ρ ∈ nontrivialZetaZerosUpTo (T+1), w ρ ≤ (∑ ρ ∈ U, w ρ) + _ + _
    have h₁ := Finset.sum_le_sum_of_subset (f := w) hs
    have h₂ := sum_union_le_nat U (P ∪ M) w
    have h₃ := sum_union_le_nat P M w
    omega
  have hplus := sum_analyticOrderNatAt_fourWindow_le_of_riemannHypothesis hRH
    (y := T) (by simpa [abs_of_nonneg (by linarith : 0 ≤ T)])
  have hminus := sum_analyticOrderNatAt_fourWindow_le_of_riemannHypothesis hRH
    (y := -T) (by simpa [abs_neg, abs_of_nonneg (by linarith : 0 ≤ T)])
  simp only [abs_neg, abs_of_nonneg (by linarith : 0 ≤ T)] at hplus hminus
  have hnr : (weightedZeroCountingFunction (T+1) : ℝ) ≤ weightedZeroCountingFunction T +
      ((∑ ρ ∈ P, w ρ : ℕ) : ℝ) + ((∑ ρ ∈ M, w ρ : ℕ) : ℝ) := by exact_mod_cast hn
  dsimp only [P, M, w] at hnr
  linarith

/-- The increment in the multiplicity-weighted zero count across a unit-height window is
logarithmic under RH. -/
theorem weightedZeroCounting_unitWindow_isBigO (hRH : RiemannHypothesis) :
    (fun T : ℝ ↦ (weightedZeroCountingFunction (T+1) : ℝ) - weightedZeroCountingFunction T)
      =O[atTop] Real.log := by
  apply Asymptotics.IsBigO.of_bound (1024/41 : ℝ)
  filter_upwards [eventually_ge_atTop (8 : ℝ)] with T hT
  have hpos : 0 < T := by linarith
  have hsub : nontrivialZetaZerosUpTo T ⊆ nontrivialZetaZerosUpTo (T+1) := by
    intro ρ hρ
    obtain ⟨hz, ht⟩ := mem_nontrivialZetaZerosUpTo.mp hρ
    exact mem_nontrivialZetaZerosUpTo.mpr ⟨hz, by linarith⟩
  have hmono : weightedZeroCountingFunction T ≤ weightedZeroCountingFunction (T+1) :=
    Finset.sum_le_sum_of_subset hsub
  have hmono' : (weightedZeroCountingFunction T : ℝ) ≤ weightedZeroCountingFunction (T+1) :=
    Nat.cast_le.mpr hmono
  simp only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hmono'),
    abs_of_nonneg (Real.log_nonneg (by linarith : 1 ≤ T))]
  have hlogs := Real.log_le_log (by linarith : 0 < T+4)
    (show T+4 ≤ T^2 by nlinarith [sq_nonneg (T-4)])
  rw [Real.log_pow] at hlogs
  norm_num at hlogs
  calc
    _ ≤ (512 / 41 : ℝ) * Real.log (T+4) := weightedZeroCounting_unitWindow_le hRH hT
    _ ≤ (512 / 41 : ℝ) * (2 * Real.log T) := mul_le_mul_of_nonneg_left hlogs (by norm_num)
    _ = _ := by ring

#print axioms RiemannSchmidt.one_sub_riemannZeta₀_eq_of_re_pos
#print axioms RiemannSchmidt.analyticOrderAt_riemannZeta_ne_top
#print axioms sum_analyticOrderNatAt_fourWindow_le_of_riemannHypothesis
#print axioms weightedZeroCountingFunction_le_sixteen_fifths
#print axioms weightedZeroCounting_unitWindow_le
#print axioms weightedZeroCounting_unitWindow_isBigO

end CarryForward.Targets
