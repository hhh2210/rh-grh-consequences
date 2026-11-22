import Targets
import Cryptids.Semantics.Riemann.WeightedStieltjes
import Cryptids.Semantics.Riemann.HorizontalBounds

/-!
# Cramér's short-interval theorem

Subtract the two adjacent first differences of the integrated Chebyshev function before
estimating the zeros. Below height `x / h`, each normalized second difference is bounded
by `h / √x`. Above that height, sum the inverse-square bound for each first difference.
With `h = K * √x * log x`, the total error is smaller than the main term for large `K`.
-/

open MeasureTheory Set intervalIntegral Real Filter Asymptotics

namespace CarryForward.Targets

private theorem norm_cpow_increment_div_le {ρ : ℂ} (hre : ρ.re = 1 / 2)
    {x t h : ℝ} (hx : 0 < x) (hxt : x ≤ t) (hh : 0 ≤ h) :
    ‖(((t + h : ℝ) : ℂ) ^ ρ - (t : ℂ) ^ ρ) / ρ‖ ≤ h / Real.sqrt x := by
  have he : (ρ - 1).re = -(1 / 2 : ℝ) := by rw [Complex.sub_re, hre]; norm_num
  have hi := integral_cpow (a := t) (b := t + h) (r := ρ - 1)
    (Or.inl (by rw [he]; norm_num))
  rw [sub_add_cancel] at hi
  rw [← hi]
  have hbound : ‖∫ u : ℝ in t..t + h, (u : ℂ) ^ (ρ - 1)‖ ≤
      (Real.sqrt x)⁻¹ * |t + h-t| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro u hu
    rw [uIoc_of_le (by linarith)] at hu
    have hxu := hxt.trans hu.1.le
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (hx.trans_le hxu), he, Real.sqrt_eq_rpow,
      ← Real.rpow_neg hx.le]
    exact Real.rpow_le_rpow_of_nonpos hx hxu (by norm_num)
  simpa [abs_of_nonneg hh, div_eq_mul_inv, mul_comm] using hbound

/-- Taking the difference of adjacent equal-length averages cancels the zero
denominator uniformly in its height on the critical line. -/
theorem norm_adjacent_cpow_averages_sub_le {ρ : ℂ} (hre : ρ.re = 1 / 2)
    {x h : ℝ} (hx : 0 < x) (hh : 0 < h) :
    ‖(∫ t : ℝ in x + h..x + h + h, (t : ℂ) ^ ρ) / ((h : ℂ) * ρ) -
      (∫ t : ℝ in x..x + h, (t : ℂ) ^ ρ) / ((h : ℂ) * ρ)‖ ≤ h / Real.sqrt x := by
  let f (t : ℝ) := (t : ℂ) ^ ρ
  have hi (a b : ℝ) : IntervalIntegrable f volume a b :=
    intervalIntegrable_cpow (Or.inl (by rw [hre]; norm_num))
  have hi' : IntervalIntegrable (fun t ↦ f (t + h)) volume x (x + h) :=
    (IntervalIntegrable.comp_add_right_iff (by finiteness)).mpr (hi _ _)
  have hrepr : (∫ t : ℝ in x + h..x + h + h, f t) / ((h : ℂ) * ρ) -
      (∫ t : ℝ in x..x + h, f t) / ((h : ℂ) * ρ) =
      (∫ t : ℝ in x..x + h, (f (t + h) - f t) / ρ) / (h : ℂ) := by
    rw [intervalIntegral.integral_div, intervalIntegral.integral_sub hi' (hi _ _), integral_comp_add_right, div_div, mul_comm ρ]
    ring
  change ‖_‖ ≤ _
  rw [show (fun t : ℝ ↦ (t : ℂ) ^ ρ) = f from rfl, hrepr, norm_div,
    Complex.norm_real, Real.norm_of_nonneg hh.le, div_le_iff₀ hh]
  have hb : ‖∫ t : ℝ in x..x + h, (f (t + h) - f t) / ρ‖ ≤
      h / Real.sqrt x * |x + h-x| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t ht
    rw [uIoc_of_le (by linarith)] at ht
    exact norm_cpow_increment_div_le hre hx ht.1.le hh.le
  simpa [abs_of_pos hh] using hb

open Finset
open Complex (I)
open ConjectureMachines.Semantics.Riemann.WeightedStieltjes

private noncomputable def zeroSum (s : Finset ℂ) (x h : ℝ) : ℂ :=
  ∑ ρ ∈ s, (analyticOrderNatAt riemannZeta ρ : ℂ) * smoothedZeroTerm x h ρ

/-- The low zeros in the triangularly smoothed explicit formula contribute at most
their multiplicity-weighted count times the width divided by the square root of the left endpoint. -/
private theorem norm_low_zeroSum_sub_le (hRH : RiemannHypothesis) {x h T : ℝ}
    (hx : 0 < x) (hh : 0 < h) :
    ‖zeroSum (nontrivialZetaZerosUpTo T) (x + h) h - zeroSum (nontrivialZetaZerosUpTo T) x h‖ ≤
      weightedZeroCountingFunction T * (h / Real.sqrt x) := by
  classical
  unfold zeroSum weightedZeroCountingFunction
  push_cast
  rw [← Finset.sum_sub_distrib, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (sum_le_sum fun ρ hρ ↦ ?_)
  rw [← mul_sub, norm_mul, Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  obtain ⟨hz, _⟩ := mem_nontrivialZetaZerosUpTo.mp hρ
  have hre := hRH ρ hz.1 hz.2.1 hz.2.2
  rw [smoothedZeroTerm_eq_integral_div _ _ (by linarith : 0 < ρ.re),
    smoothedZeroTerm_eq_integral_div _ _ (by linarith : 0 < ρ.re)]
  exact norm_adjacent_cpow_averages_sub_le hre hx hh

private theorem norm_zeroSum_sub_le (hRH : RiemannHypothesis) {x h T U : ℝ}
    (hx : 0 < x) (hh : 0 < h) (hT : 6 ≤ T) (hTU : T ≤ U) :
    ‖zeroSum (nontrivialZetaZerosUpTo U) (x + h) h - zeroSum (nontrivialZetaZerosUpTo U) x h‖ ≤
      weightedZeroCountingFunction T * (h / Real.sqrt x) +
      ((2 * (x + h + h) ^ (3 / 2 : ℝ) / h) + (2 * (x + h) ^ (3 / 2 : ℝ) / h)) *
        ((2 * (16 / 5) * Real.log T + 2 * (16 / 5) + 2 * (11 / 5)) / T) := by
  let lo := nontrivialZetaZerosUpTo T
  let hi := nontrivialZetaZerosBetween T U
  have hs (y : ℝ) : zeroSum (nontrivialZetaZerosUpTo U) y h = zeroSum lo y h + zeroSum hi y h :=
    sum_nontrivialZetaZerosUpTo_eq_add_between hTU _
  have ht : 0 < T := by linarith
  have hf := sum_weighted_inv_sq_nontrivialZetaZerosBetween_le_of_riemannVonMangoldt
    (a := 16 / 5) (C := 11 / 5) (D := 0) ht hTU (by norm_num) (by norm_num)
    (fun t h ↦ by simpa using ConjectureMachines.Semantics.Riemann.VonMangoldtCount.weightedZeroCountingFunction_le_sixteen_fifths hRH (hT.trans h.1))
  simp only [mul_zero, zero_div, add_zero] at hf
  have hhf (y : ℝ) (hy : 0 < y) : ‖zeroSum hi y h‖ ≤ _ :=
    (norm_sum_smoothedZeroTerm_between_le_of_riemannHypothesis hRH hy hh ht).trans
      (mul_le_mul_of_nonneg_left hf (by positivity))
  rw [hs, hs, add_sub_add_comm]
  exact (norm_add_le _ _).trans (add_le_add (norm_low_zeroSum_sub_le hRH hx hh)
    ((norm_sub_le _ _).trans (by rw [add_mul]; exact add_le_add (hhf _ (by linarith)) (hhf _ hx))))

private theorem remainder_increment_le {y h c U : ℝ} (hy : 1 ≤ y) (hh : 0 < h)
    (hyc : y + h ≤ c + h) (hU : 0 < U)
    (hz : ∀ ρ ∈ nontrivialZetaZerosUpTo U, |ρ.im| < U) :
    |(psi1ContourRemainder (y + h) U - psi1ContourRemainder y U) / h| ≤
    4 * (c + h) ^ (3:ℝ) / (Real.pi * h * U) +
    (contourBoundaryError (y + h) (-1 / 4) U + contourBoundaryError y (-1 / 4) U) / h := by
  have h₁ := abs_psi1ContourRemainder_le_of_neg hy hU
    (by norm_num : (-1 / 2:ℝ) < -1 / 4) (by norm_num) hz
  have h₂ := abs_psi1ContourRemainder_le_of_neg (show 1 ≤ y + h by linarith) hU
    (by norm_num : (-1 / 2:ℝ) < -1 / 4) (by norm_num) hz
  have hpow : y ^ (3:ℝ) ≤ (c + h) ^ (3:ℝ) := Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
  have hpow' : (y + h) ^ (3:ℝ) ≤ (c + h) ^ (3:ℝ) :=
    Real.rpow_le_rpow (by linarith) hyc (by norm_num)
  rw [abs_div, abs_of_pos hh, div_le_iff₀ hh]
  have hpi := Real.pi_pos
  have hs := (abs_sub (psi1ContourRemainder (y + h) U) (psi1ContourRemainder y U)).trans (add_le_add h₂ h₁)
  apply hs.trans
  field_simp
  nlinarith only [hpow, hpow']

private theorem psi_increment_lower (hRH : RiemannHypothesis) {x h T : ℝ}
    (hx : 1 ≤ x) (hh : 0 < h) (hT : 6 ≤ T) :
    h - ((weightedZeroCountingFunction T * (h / Real.sqrt x) +
      (2 * (x + h + h) ^ (3 / 2 : ℝ) / h + 2 * (x + h) ^ (3 / 2 : ℝ) / h) *
        ((2 * (16 / 5) * Real.log T + 2 * (16 / 5) + 2 * (11 / 5)) / T)) +
      2 * (32 * (2 * 1 + 85) / (Real.pi * h) * (x + h + h) ^ (3 / 4 : ℝ) + 1)) ≤
        Chebyshev.psi (x + h + h) - Chebyshev.psi x := by
  obtain ⟨C, hC, hheights⟩ :=
    ConjectureMachines.Semantics.Riemann.HorizontalBounds.exists_zero_free_height_with_log_pow_five_bound hRH hT
  have hxh : 1 ≤ x + h - h := by linarith
  obtain ⟨U, hTU, hz, htail⟩ :=
    exists_zero_free_height_with_small_tailAndHorizontal hxh hh hC hheights 1 (by norm_num)
  have hU : 0 < U := by linarith
  have hv := contourLeftVerticalDiffError_neg_one_fourth_le hxh hh hU.le (A:= 1) (B:= 85)
    (by norm_num) (by norm_num) (fun t => by
      have he : (((-1 / 4:ℝ):ℂ) + (t:ℂ)*I) = (-1 / 4:ℂ) + (t:ℂ)*I := by push_cast; ring
      rw [he, neg_div, norm_neg, ← logDeriv_apply, one_mul]
      exact ConjectureMachines.Semantics.Riemann.DigammaBinet.norm_logDeriv_riemannZeta_leftVertical_le_eighty_five t)
  have hcont := (contourDiffError_le_leftVertical_add_tailAndHorizontal (x + h) h (-1 / 4) U).trans
    (add_le_add hv htail)
  let D (y : ℝ) := (psi1ContourRemainder (y + h) U - psi1ContourRemainder y U) / h
  have hb : |D x| ≤ contourDiffError (x + h) h (-1 / 4) U := by
    refine (remainder_increment_le (c:=x + h) hx hh (by linarith) hU hz).trans ?_
    unfold contourDiffError
    rw [add_sub_cancel_right]
    exact add_le_add le_rfl (le_max_right _ _)
  have hf : |D (x + h)| ≤ contourDiffError (x + h) h (-1 / 4) U :=
    (remainder_increment_le (by linarith : 1 ≤ x + h) hh le_rfl hU hz).trans
      (add_le_add le_rfl (le_max_left _ _))
  let Z (y : ℝ) := zeroSum (nontrivialZetaZerosUpTo U) y h
  have hid (y : ℝ) : (psi1 (y + h) - psi1 y)/h - (y + h/2) =
      -Real.log (2*Real.pi) - (Z y).re + D y := by
    simpa only [Z, D, zeroSum, Complex.neg_re, sub_eq_add_neg] using
      (psi1_add_sub_div_sub_linear_eq (x₁:=y) (U:=U) hh.ne')
  have hzero := (Complex.re_le_norm (Z (x + h) - Z x)).trans (norm_zeroSum_sub_le hRH (by linarith : 0 < x) hh hT hTU)
  rw [Complex.sub_re] at hzero
  have hleft := psi_le_psi1_add_sub_div x hh
  have hright := psi1_sub_psi1_sub_div_le_psi (x + h + h) hh
  rw [add_sub_cancel_right] at hright
  linarith only [hleft, hright, hid x, hid (x + h), hzero, (abs_le.mp (hb.trans hcont)).2,
    (abs_le.mp (hf.trans hcont)).1]


private theorem eventually_width_le {K : ℝ} (hK : 0 < K) :
    ∀ᶠ x : ℝ in atTop, 6 * (K * sqrt x * log x) ≤ x := by
  have hl := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).bound
    (show 0 < 1 / (6 * K) by positivity)
  filter_upwards [hl, eventually_ge_atTop (1 : ℝ)] with x h hx
  rw [Real.norm_eq_abs, abs_of_nonneg (log_nonneg hx), ← sqrt_eq_rpow, Real.norm_eq_abs,
    abs_of_nonneg (sqrt_nonneg _)] at h
  have h' : 6 * K * log x ≤ sqrt x := by
    field_simp at h
    nlinarith only [h]
  nlinarith only [mul_le_mul_of_nonneg_right h' (sqrt_nonneg x), sq_sqrt (by linarith : 0 ≤ x)]

private theorem cramer_scale_bound {x h : ℝ} (hx : 1 ≤ x) (hl : 1 ≤ log x)
    (hsh : sqrt x ≤ h) (h6 : 6 * h ≤ x) :
    ((16 / 5 * (x / h) * log (x / h) + 11 / 5 * (x / h)) * (h / sqrt x) +
      (2 * (x + h + h) ^ (3 / 2 : ℝ) / h + 2 * (x + h) ^ (3 / 2 : ℝ) / h) *
        ((2 * (16 / 5) * log (x / h) + 2 * (16 / 5) + 2 * (11 / 5)) / (x / h))) +
      2 * (32 * (2 * 1 + 85) / (π * h) * (x + h + h) ^ (3 / 4 : ℝ) + 1) ≤
       24_000 * sqrt x * log x := by
  have hx0 : 0 < x := by linarith
  have hs := sqrt_pos.2 hx0
  have hs1 : 1 ≤ sqrt x := by simpa using sqrt_le_sqrt hx
  have hh : 0 < h := hs.trans_le hsh
  have ht : 6 ≤ x / h := (le_div_iff₀ hh).2 h6
  have htx : x / h ≤ x := div_le_self hx0.le (hs1.trans hsh)
  have hlog := log_le_log (by positivity : 0 < x / h) htx
  have hy (y : ℝ) (hy0 : 1 ≤ y) (hyx : y ≤ 4 * x) : y ^ (3 / 2 : ℝ) ≤ 8 * x * sqrt x := by
    calc y ^ (3 / 2 : ℝ) ≤ (4 * x) ^ (3 / 2 : ℝ) := rpow_le_rpow (by linarith) hyx (by norm_num)
      _ = 8 * x * sqrt x := by
        rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, rpow_add (by positivity), rpow_one,
          ← sqrt_eq_rpow, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
        norm_num; ring
  have hy0 : 1 ≤ x + h + h := by linarith
  have hya : x + h + h ≤ 4 * x := by linarith
  have h3 : (x + h + h) ^ (3 / 4 : ℝ) ≤ 4 * x :=
    (calc _ ≤ (x + h + h) ^ (1:ℝ) := rpow_le_rpow_of_exponent_le hy0 (by norm_num)
          _ = _ := rpow_one _).trans hya
  have hb1 := hy _ hy0 hya
  have hb2 := hy (x + h) (by linarith) (by linarith)
  have hsx := sq_sqrt hx0.le
  have hlo : (16 / 5 * (x / h) * log (x / h) + 11 / 5 * (x / h)) * (h / sqrt x) ≤
      6 * sqrt x * log x := by
    field_simp
    nlinarith only [mul_nonneg hx0.le (sub_nonneg.mpr hlog), mul_nonneg hx0.le (sub_nonneg.mpr hl),
      mul_pos hx0 (lt_of_lt_of_le zero_lt_one hl), hsx, congrArg (fun z => z * log x) hsx]
  have htail : (2 * (x + h + h) ^ (3 / 2 : ℝ) / h + 2 * (x + h) ^ (3 / 2 : ℝ) / h) *
        ((2 * (16 / 5) * log (x / h) + 2 * (16 / 5) + 2 * (11 / 5)) / (x / h)) ≤
        576 * sqrt x * log x := by
    calc _ ≤ (2*(8 * x * sqrt x)/h + 2*(8 * x * sqrt x)/h) * (18*log x/(x / h)) := by
              have hlT : 0 ≤ log (x / h) := log_nonneg (by linarith)
              apply mul_le_mul
              · gcongr
              · apply div_le_div_of_nonneg_right _ (by positivity)
                linarith
              · positivity
              · positivity
         _ = _ := by field_simp; ring
  have hpi : 1 ≤ π := by linarith [Real.two_le_pi]
  have hv : 32 * (2 * 1 + 85) / (π * h) * (x + h + h) ^ (3 / 4 : ℝ) ≤ 11_136 * sqrt x := by
    calc _ ≤ 2784 / h * (4 * x) := by
              norm_num
              gcongr
              simpa using mul_le_mul_of_nonneg_right hpi hh.le
         _ ≤ 11_136 * sqrt x := by
           rw [div_mul_eq_mul_div, div_le_iff₀ hh]
           nlinarith only [hsx, mul_le_mul_of_nonneg_left hsh hs.le]
  nlinarith only [hlo, htail, hv, hs1, mul_nonneg hs.le (sub_nonneg.mpr hl)]


private theorem exists_prime_of_theta_lt {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y)
    (hθ : Chebyshev.theta x < Chebyshev.theta y) :
    ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ y := by
  by_contra! hn
  have he : Nat.primesLE ⌊x⌋₊ = Nat.primesLE ⌊y⌋₊ := by
    apply Finset.Subset.antisymm (Nat.primesLE_mono (Nat.floor_mono hxy))
    intro p hp
    obtain ⟨hpy, hprime⟩ := Nat.mem_primesLE.mp hp
    have hy' := (Nat.le_floor_iff (hx.trans hxy)).1 hpy
    refine Nat.mem_primesLE.mpr ⟨(Nat.le_floor_iff hx).2 ?_, hprime⟩
    exact le_of_not_gt fun hxp ↦ (hn p hprime hxp).not_ge hy'
  simp only [Chebyshev.theta_eq_sum_primesLE, he, lt_self_iff_false] at hθ

/-- Cramér's short-interval theorem under the Riemann hypothesis. -/
theorem primeInShortInterval_of_riemannHypothesis (hRH : RiemannHypothesis) : PrimeInShortInterval := by
  obtain ⟨D, hD⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  let K : ℝ := 24_001 + 2 * |D|
  have hK : 1 ≤ K := by dsimp [K]; linarith [abs_nonneg D]
  have hw := eventually_width_le (K:=K) (by linarith)
  obtain ⟨x₀, hw⟩ := eventually_atTop.1 hw
  refine ⟨2 * K, max x₀ (Real.exp 1), fun x hx ↦ ?_⟩
  have hxexp := (le_max_right x₀ _).trans hx
  have hl : 1 ≤ Real.log x := by simpa using Real.log_le_log (Real.exp_pos _) hxexp
  have hx1 : 1 ≤ x := (Real.one_le_exp (by norm_num : (0:ℝ) ≤ 1)).trans hxexp
  have hx0 : 0 < x := by linarith
  let h := K * Real.sqrt x * Real.log x
  have hsh : Real.sqrt x ≤ h := by
    calc _ ≤ K * Real.sqrt x := le_mul_of_one_le_left (Real.sqrt_nonneg _) hK
         _ ≤ _ := le_mul_of_one_le_right (by positivity) hl
  have hh : 0 < h := (Real.sqrt_pos.2 hx0).trans_le hsh
  have h6 : 6 * h ≤ x := hw x ((le_max_left _ _).trans hx)
  have ht := (le_div_iff₀ hh).2 h6
  have hN := ConjectureMachines.Semantics.Riemann.VonMangoldtCount.weightedZeroCountingFunction_le_sixteen_fifths hRH ht
  have he := psi_increment_lower hRH hx1 hh ht
  have hscale := cramer_scale_bound hx1 hl hsh h6
  have hψ : h - 24_000 * Real.sqrt x * Real.log x ≤ Chebyshev.psi (x + h + h) - Chebyshev.psi x := by
    linarith only [he, hscale, mul_le_mul_of_nonneg_right hN (show 0 ≤ h / Real.sqrt x by positivity)]
  have hs : Real.sqrt (x + h + h) ≤ 2 * Real.sqrt x := by
    calc _ ≤ Real.sqrt (4 * x) := Real.sqrt_le_sqrt (by linarith)
         _ = _ := by rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]; norm_num
  have hδ := (hD (x + h + h)).trans (mul_le_mul (le_abs_self D) hs (Real.sqrt_nonneg _) (abs_nonneg D))
  have htlt : Chebyshev.theta x < Chebyshev.theta (x + h + h) := by
    have hrem := mul_nonneg (mul_nonneg (abs_nonneg D) (Real.sqrt_nonneg x)) (sub_nonneg.mpr hl)
    dsimp [h, K] at hψ
    nlinarith only [hψ, hδ, Chebyshev.theta_le_psi x, hrem, Real.sqrt_pos.2 hx0,
      mul_pos (Real.sqrt_pos.2 hx0) (by linarith : 0 < Real.log x)]
  obtain ⟨p, hp, hlp, hpr⟩ := exists_prime_of_theta_lt hx0.le (by linarith) htlt
  exact ⟨p, hp, hlp, hpr.trans_eq (by dsimp [h]; ring)⟩

#print axioms primeInShortInterval_of_riemannHypothesis
end CarryForward.Targets
