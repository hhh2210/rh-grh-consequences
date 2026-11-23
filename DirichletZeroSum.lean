/-
The local principal-part argument is adapted from Google LLC's Cryptids,
WeightedStieltjes.lean, commit 3647718b5df22e1a61462dec0376bd204526285a.
Copyright (c) 2026 Google LLC. Licensed under Apache 2.0.
Modifications: generalize the logarithmic derivative and apply it to Dirichlet characters.
-/
import Ankeny

open Complex Set Finset Filter MeasureTheory
open scoped Topology
open ConjectureMachines.Semantics.Riemann.WeightedStieltjes

namespace CarryForward.Targets

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

private theorem L_two_ne_zero (χ : DirichletCharacter ℂ q) : χ.LFunction 2 ≠ 0 :=
  χ.LFunction_ne_zero_of_one_le_re (Or.inr (by norm_num)) (by norm_num)

private theorem zero_complement (hχ : χ ≠ 1) :
    {z : ℂ | χ.LFunction z = 0}ᶜ ∈ codiscrete ℂ := by
  have ha : AnalyticOnNhd ℂ χ.LFunction univ :=
    fun z _ ↦ (DirichletCharacter.differentiable_LFunction hχ).analyticAt z
  exact ha.preimage_zero_mem_codiscrete (L_two_ne_zero χ)

/-- The zeros in a finite contour rectangle, listed once per distinct point.
Their analytic multiplicities enter the residue sum separately. -/
noncomputable def characterZeros (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (a T : ℝ) : Finset ℂ := by
  classical
  have h := mem_codiscrete'.mp (zero_complement hχ)
  have hc : IsCompact (closedRect a 2 T) := isCompact_Icc.reProdIm isCompact_Icc
  have hf : (closedRect a 2 T ∩ {z | χ.LFunction z = 0}).Finite :=
    (hc.inter_right (by simpa using h.1)).finite ((show IsDiscrete {z | χ.LFunction z = 0} by
      simpa using h.2).mono inter_subset_right)
  exact hf.toFinset

@[simp] theorem mem_characterZeros (hχ : χ ≠ 1) {a T : ℝ} {z : ℂ} :
    z ∈ characterZeros χ hχ a T ↔ z ∈ closedRect a 2 T ∧ χ.LFunction z = 0 := by
  classical
  simp [characterZeros]

/-- Under primitive GRH each unit interval of positive heights contains a rectangle
with all zeros strictly inside. This gives qualitative avoidance of boundary zeros. -/
theorem exists_character_contour_height (hg : PrimitiveDirichletLZerosOnLine)
    (hp : χ.IsPrimitive) (hχ : χ ≠ 1) {U : ℝ} (hU : 0 < U) :
    ∃ T ∈ Set.Ioo U (U + 1), 0 < T ∧ ∀ z ∈ characterZeros χ hχ (1 / 4) T,
      z ∈ openRect (1 / 4) 2 T := by
  classical
  let Z := characterZeros χ hχ (1 / 4) (U + 1)
  obtain ⟨T, hT, hfree⟩ := (Set.Ioo_infinite (by linarith : U < U + 1)).exists_notMem_finset
    (Z.image fun z ↦ |z.im|)
  refine ⟨T, hT, hU.trans hT.1, fun z hz ↦ ?_⟩
  obtain ⟨hr, hzero⟩ := (mem_characterZeros hχ).1 hz
  have hlt : z.re < 1 := lt_of_not_ge fun h ↦
    χ.LFunction_ne_zero_of_one_le_re (Or.inl hχ) h hzero
  have hline := hg q χ hp z (by linarith [hr.1.1]) hlt hzero
  have hz' : z ∈ Z := (mem_characterZeros hχ).2
    ⟨⟨hr.1, ⟨by linarith [hr.2.1, hT.2], by linarith [hr.2.2, hT.2]⟩⟩, hzero⟩
  have him : |z.im| < T := lt_of_le_of_ne (abs_le.mpr hr.2) <| fun e ↦
    hfree (e ▸ Finset.mem_image_of_mem (fun z : ℂ ↦ |z.im|) hz')
  exact ⟨⟨by linarith, by linarith⟩, abs_lt.mp him⟩

private theorem logDeriv_principal_part {f u : ℂ → ℂ} {p : ℂ} {m : ℕ}
    (hu : AnalyticAt ℂ u p) (hup : u p ≠ 0)
    (he : f =ᶠ[𝓝 p] fun z ↦ (z - p) ^ m * u z) :
    ∀ᶠ z in 𝓝[≠] p, deriv f z / f z = m / (z - p) + deriv u z / u z := by
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds he,
    nhdsWithin_le_nhds he.deriv, nhdsWithin_le_nhds (hu.continuousAt.eventually_ne hup),
    nhdsWithin_le_nhds hu.eventually_analyticAt] with z hz h hd hnu hau
  have hn : z - p ≠ 0 := sub_ne_zero.mpr hz
  rw [h, hd, ← logDeriv_apply, logDeriv_fun_mul (f := fun w : ℂ ↦ (w - p) ^ m) (g := u) z (pow_ne_zero _ hn) hnu
    (by fun_prop) hau.differentiableAt, logDeriv_fun_pow (f := fun w : ℂ ↦ w - p) (differentiableAt_id.sub_const p)]
  simp [logDeriv_apply, div_eq_mul_inv]

/-- The coefficient of the simple pole of the Perron integrand at a zero of multiplicity m. -/
noncomputable def characterResidue (χ : DirichletCharacter ℂ q) (x : ℝ) (ρ : ℂ) : ℂ :=
  -(analyticOrderNatAt χ.LFunction ρ : ℂ) * smoothedPerronKernel x ρ

private theorem principalPart_limit (hχ : χ ≠ 1) {x : ℝ} (hx : 0 < x) {ρ : ℂ}
    (hρ : 0 < ρ.re) :
    ∃ L : ℂ, Tendsto (fun s ↦ characterIntegrand χ x s - characterResidue χ x ρ / (s - ρ))
      (𝓝[≠] ρ) (𝓝 L) := by
  have ha : AnalyticOnNhd ℂ χ.LFunction univ :=
    fun z _ ↦ (DirichletCharacter.differentiable_LFunction hχ).analyticAt z
  have hfin := ha.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (mem_univ (2 : ℂ)) (mem_univ ρ) (by
      rw [(ha 2 (mem_univ _)).analyticOrderAt_eq_zero.mpr (L_two_ne_zero χ)]; exact ENat.zero_ne_top)
  obtain ⟨u, hu, hne, he⟩ := (ha ρ (mem_univ _)).analyticOrderAt_ne_top.mp hfin
  let m := analyticOrderNatAt χ.LFunction ρ
  have hlog := logDeriv_principal_part (m := m) hu hne (by simpa only [smul_eq_mul] using he)
  have h0 : ρ ≠ 0 := by rintro rfl; simp at hρ
  have h1 : ρ ≠ -1 := by rintro rfl; norm_num at hρ
  have hk := differentiableAt_smoothedPerronKernel hx h0 h1
  have hd := (tendsto_sub_div_sub_of_differentiableAt hk).const_mul (-(m : ℂ))
  have hu' : ContinuousAt (fun s ↦ deriv u s / u s * smoothedPerronKernel x s) ρ :=
    (hu.deriv.continuousAt.div hu.continuousAt hne).mul hk.continuousAt
  refine ⟨_, (hd.sub (hu'.tendsto.mono_left nhdsWithin_le_nhds)).congr' ?_⟩
  filter_upwards [hlog] with s hs
  simp only [characterIntegrand, characterResidue, neg_div]
  rw [hs]
  dsimp [m]
  ring

private theorem differentiableAt_characterIntegrand (hχ : χ ≠ 1) {x : ℝ} (hx : 0 < x)
    {z : ℂ} (hz : 0 < z.re) (hn : χ.LFunction z ≠ 0) :
    DifferentiableAt ℂ (characterIntegrand χ x) z := by
  have ha := (DirichletCharacter.differentiable_LFunction hχ).analyticAt z
  exact ((ha.deriv.differentiableAt.neg.div ha.differentiableAt hn).mul
    (differentiableAt_smoothedPerronKernel hx (by rintro rfl; simp at hz)
      (by rintro rfl; norm_num at hz)))

/-- The tails of the right Perron line vanish for every fixed positive smoothing length.
The log-derivative on that line is bounded uniformly in the character. -/
theorem tendsto_truncated_characterPerron (hχ : χ ≠ 1) {x : ℝ} (hx : 0 < x) :
    Tendsto (fun T : ℝ ↦ (2 * (Real.pi : ℂ))⁻¹ *
      ∫ t in (-T)..T, characterIntegrand χ x (2 + (t : ℂ) * I))
      atTop (𝓝 (characterPerron χ x 2)) := by
  have hcont : Continuous (fun t : ℝ ↦ characterIntegrand χ x (2 + (t : ℂ) * I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hc : ContinuousAt (fun u : ℝ ↦ (2 : ℂ) + (u : ℂ) * I) t := by fun_prop
    exact (differentiableAt_characterIntegrand hχ hx (by simp : 0 < (2 + (t : ℂ) * I).re)
      (χ.LFunction_ne_zero_of_one_le_re (Or.inl hχ) (by simp))).continuousAt.comp (f := fun u : ℝ ↦ (2 : ℂ) + (u : ℂ) * I) hc
  have hint := (integrable_smoothedPerronKernel hx (by norm_num : (0 : ℝ) < 2)).norm.const_mul 2
  have hfull : MeasureTheory.Integrable (fun t : ℝ ↦ characterIntegrand χ x (2 + (t : ℂ) * I)) := by
    refine hint.mono' hcont.aestronglyMeasurable (Eventually.of_forall fun t ↦ ?_)
    simp only [characterIntegrand, norm_mul]
    simpa using mul_le_mul_of_nonneg_right (norm_character_logDeriv_two_le χ t)
      (norm_nonneg (smoothedPerronKernel x (2 + (t : ℂ) * I)))
  simpa [characterPerron] using (intervalIntegral_tendsto_integral hfull
    tendsto_neg_atTop_atBot tendsto_id).const_mul ((2 * (Real.pi : ℂ))⁻¹)

/-- A finite-height explicit formula for nonprincipal Dirichlet characters. Positive
left edge avoids the trivial zeros and the poles of the smoothing kernel. -/
theorem character_rectangle_eq_sum_residues (hχ : χ ≠ 1) {x a T : ℝ}
    (hx : 0 < x) (ha : 0 < a) (ha2 : a ≤ 2) (hT : 0 ≤ T)
    (hboundary : ∀ z ∈ characterZeros χ hχ a T, z ∈ openRect a 2 T) :
    rectBoundaryIntegral (characterIntegrand χ x) a 2 T =
      2 * (Real.pi : ℂ) * I * ∑ z ∈ characterZeros χ hχ a T, characterResidue χ x z := by
  classical
  let P := characterZeros χ hχ a T
  let M := characterIntegrand χ x
  let r := characterResidue χ x
  let v (z : ℂ) := limUnder (𝓝[≠] z) (fun s ↦ M s - r z / (s - z))
  let F := removePoles M P r v
  have hd (z : ℂ) (hz : z ∈ closedRect a 2 T) : DifferentiableAt ℂ F z := by
    have hpos := ha.trans_le hz.1.1
    by_cases hp : z ∈ P
    · apply differentiableAt_removePoles_of_mem hp
      · have havoid : ∀ᶠ s in 𝓝[≠] z, χ.LFunction s ≠ 0 := by
          change {s : ℂ | χ.LFunction s = 0}ᶜ ∈ 𝓝[≠] z
          simpa only [compl_compl] using disjoint_principal_right.mp ((mem_codiscrete.mp (zero_complement hχ)) z)
        have hopen : ∀ᶠ s in 𝓝 z, 0 < s.re :=
          (isOpen_lt continuous_const continuous_re).mem_nhds hpos
        filter_upwards [havoid, nhdsWithin_le_nhds hopen] with s hs hs'
        exact differentiableAt_characterIntegrand hχ hx hs' hs
      · obtain ⟨L, hL⟩ := principalPart_limit hχ hx hpos
        change Tendsto _ _ (𝓝 (limUnder _ _))
        rwa [hL.limUnder_eq]
    · apply differentiableAt_removePoles_of_notMem hp
      exact differentiableAt_characterIntegrand hχ hx hpos fun he ↦
        hp ((mem_characterZeros hχ).2 ⟨hz, he⟩)
  refine rectBoundaryIntegral_eq_sum_residues_off_countable (F := F) ha2 hT countable_empty
    hboundary (fun z hz ↦ (hd z hz).continuousAt.continuousWithinAt) (fun z hz ↦ ?_) ?_
  · exact hd z ⟨⟨hz.1.1.1.le, hz.1.1.2.le⟩, ⟨hz.1.2.1.le, hz.1.2.2.le⟩⟩
  · intro z hz
    dsimp only [F]
    rw [removePoles_of_notMem M P r v hz.2]
    abel

/-- A normalized vertical or horizontal edge of the smoothed Perron contour.
The orientations are supplied by the signed rectangle identity. -/
noncomputable def characterVertical (χ : DirichletCharacter ℂ q) (x c T : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ))⁻¹ * ∫ t in (-T)..T, characterIntegrand χ x ((c : ℂ) + (t : ℂ) * I)

/-- Horizontal edge from real part `a` to 2 at height `t`. -/
noncomputable def characterHorizontal (χ : DirichletCharacter ℂ q) (x a t : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ) * I)⁻¹ * ∫ σ in a..2, characterIntegrand χ x ((σ : ℂ) + (t : ℂ) * I)

/-- Signed finite-height explicit formula for the truncated right edge. -/
theorem characterPerron_truncated_eq (hχ : χ ≠ 1) {x a T : ℝ}
    (hx : 0 < x) (ha : 0 < a) (ha2 : a ≤ 2) (hT : 0 ≤ T)
    (hz : ∀ z ∈ characterZeros χ hχ a T, z ∈ openRect a 2 T) :
    characterVertical χ x 2 T = (∑ z ∈ characterZeros χ hχ a T, characterResidue χ x z) +
      characterVertical χ x a T + characterHorizontal χ x a T - characterHorizontal χ x a (-T) := by
  have h := right_vertical_integral_eq_rectBoundaryIntegral_add (characterIntegrand χ x) a 2 T
  rw [character_rectangle_eq_sum_residues hχ hx ha ha2 hT hz, inv_two_pi_I_mul_two_pi_I_mul] at h
  simpa [characterVertical, characterHorizontal, sub_eq_add_neg] using h

private theorem norm_kernel_on_line {x : ℝ} (hx : 0 < x) {z : ℂ} (hz : z.re = 1 / 2) :
    ‖smoothedPerronKernel x z‖ ≤ 4 * (x * Real.sqrt x) / (1 + z.im ^ 2) := by
  have h := norm_smoothedPerronKernel_le hx (by norm_num : (0 : ℝ) < 1 / 2) z.im
  have he : (((1 / 2 : ℝ):ℂ) + (z.im : ℂ) * I) = z := by
    rw [← hz]; exact re_add_im z
  rw [he, Real.rpow_add hx, Real.rpow_one, ← Real.sqrt_eq_rpow] at h
  apply h.trans
  have hd : 0 < (1 / 2 : ℝ) ^ 2 + z.im ^ 2 := by positivity
  have hd' : 0 < 1 + z.im ^ 2 := by positivity
  rw [← div_eq_mul_inv, div_le_div_iff₀ hd hd']
  nlinarith only [mul_nonneg (mul_nonneg hx.le (Real.sqrt_nonneg x)) (sq_nonneg z.im)]

/-- Under primitive GRH a single inverse-square height moment bounds all the residues,
uniformly in the truncation height. -/
theorem norm_character_residue_sum_le (hg : PrimitiveDirichletLZerosOnLine)
    (hp : χ.IsPrimitive) (hχ : χ ≠ 1) {x a T : ℝ} (hx : 0 < x) (ha : 0 < a) :
    ‖∑ z ∈ characterZeros χ hχ a T, characterResidue χ x z‖ ≤ 4 * (x * Real.sqrt x) *
      ∑ z ∈ characterZeros χ hχ a T, (analyticOrderNatAt χ.LFunction z : ℝ) / (1 + z.im ^ 2) := by
  classical
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (sum_le_sum fun z hz ↦ ?_)
  obtain ⟨hr, hzero⟩ := (mem_characterZeros hχ).1 hz
  have hlt : z.re < 1 := lt_of_not_ge fun h ↦ χ.LFunction_ne_zero_of_one_le_re (Or.inl hχ) h hzero
  have hline := hg q χ hp z (ha.trans_le hr.1.1) hlt hzero
  rw [characterResidue, norm_mul, norm_neg, Complex.norm_natCast]
  calc _ ≤ (analyticOrderNatAt χ.LFunction z : ℝ) * _ :=
        mul_le_mul_of_nonneg_left (norm_kernel_on_line hx hline) (Nat.cast_nonneg _)
       _ = _ := by ring

/-- The two quantitative inputs: an inverse-square zero moment, and separate estimates
for the other three edges of arbitrarily tall rectangles. No bound on the original
Perron line or on the character sum occurs in this hypothesis. -/
def PrimitiveContourBounds : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    χ.IsPrimitive → ∀ hχ : χ ≠ 1, ∀ x : ℝ, 16 ≤ x → ∀ T₀ : ℝ, ∃ T ≥ max 1 T₀,
      (∀ z ∈ characterZeros χ hχ (1 / 4) T, z ∈ openRect (1 / 4) 2 T) ∧
      (∑ z ∈ characterZeros χ hχ (1 / 4) T,
        (analyticOrderNatAt χ.LFunction z : ℝ) / (1 + z.im ^ 2)) ≤ B * Real.log q ∧
      ‖characterVertical χ x (1 / 4) T‖ ≤ B * x * Real.sqrt x * Real.log q ∧
      ‖characterHorizontal χ x (1 / 4) T‖ ≤ B * x * Real.sqrt x * Real.log q ∧
      ‖characterHorizontal χ x (1 / 4) (-T)‖ ≤ B * x * Real.sqrt x * Real.log q

/-- Use the finite-height formula along good heights and pass to the Perron integral. -/
theorem primitivePerronBound_of_contourBounds (hg : PrimitiveDirichletLZerosOnLine)
    (hb : PrimitiveContourBounds) : PrimitivePerronBound := by
  obtain ⟨B, hB, h⟩ := hb
  refine ⟨7 * B, by positivity, fun q _ χ hp hχ x hx ↦ ?_⟩
  have hx0 : 0 < x := by linarith
  -- A violation of the asserted bound persists far enough up the right line.
  by_contra! hbad
  let b := 7 * B * x * Real.sqrt x * Real.log q
  have hgap : 0 < ‖characterPerron χ x 2‖ - b := sub_pos.mpr hbad
  obtain ⟨T₀, hclose⟩ := Metric.tendsto_atTop.mp (tendsto_truncated_characterPerron hχ hx0)
    _ hgap
  obtain ⟨T, hT, hbd, hm, hv, ht, hbot⟩ := h q χ hp hχ x hx T₀
  have hT0 : 0 ≤ T := (by positivity : (0 : ℝ) ≤ 1).trans ((le_max_left _ _).trans hT)
  have htr : ‖characterVertical χ x 2 T‖ ≤ b := by
    rw [characterPerron_truncated_eq hχ hx0 (by norm_num : (0 : ℝ) < 1 / 4)
      (by norm_num) hT0 hbd]
    have hz := (norm_character_residue_sum_le hg hp hχ hx0 (by norm_num : (0 : ℝ) < 1 / 4)
      (T := T)).trans (mul_le_mul_of_nonneg_left hm (by positivity))
    apply (norm_sub_le _ _).trans
    dsimp only [b]
    linarith only [hz, hv, ht, hbot,
      norm_add_le ((∑ z ∈ characterZeros χ hχ (1 / 4) T, characterResidue χ x z) +
        characterVertical χ x (1 / 4) T) (characterHorizontal χ x (1 / 4) T),
      norm_add_le (∑ z ∈ characterZeros χ hχ (1 / 4) T, characterResidue χ x z)
        (characterVertical χ x (1 / 4) T)]
  have hc : dist (characterVertical χ x 2 T) (characterPerron χ x 2) <
      ‖characterPerron χ x 2‖ - b := hclose T ((le_max_right _ _).trans hT)
  have := norm_sub_norm_le (characterPerron χ x 2) (characterVertical χ x 2 T)
  rw [dist_comm, dist_eq_norm] at hc
  linarith

/-- Conditional Ankeny bound for all moduli from archive GRH and the uniform contour estimates. -/
theorem ankenyBound_of_dirichletGRH_of_contourBounds (hg : DirichletLZerosOnLine)
    (hb : PrimitiveContourBounds) : AnkenyBound :=
  ankenyBound_of_primitivePerronBound (primitivePerronBound_of_contourBounds
    (dirichletLZerosOnLine_iff_primitive.mp hg) hb)

/-- End-to-end conditional reduction from archive GRH and the two contour estimates.
The numeric cutoff is absolute and works at every odd composite. -/
theorem miller_of_dirichletGRH_of_contourBounds (hg : DirichletLZerosOnLine)
    (hb : PrimitiveContourBounds) :
    ∃ C : ℝ, ∀ n : ℕ, 2 < n → Odd n →
      (n.Prime ↔ ∀ a : ℕ, 2 ≤ a → a < n → (a : ℝ) ≤ C * Real.log n ^ 2 →
        IsStrongProbablePrime n a) :=
  miller_of_ankenyBound (ankenyBound_of_dirichletGRH_of_contourBounds hg hb)

end CarryForward.Targets
