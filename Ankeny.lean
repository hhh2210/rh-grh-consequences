import MillerCharacter
import MillerSubgroup
import Cryptids.Semantics.Riemann.WeightedStieltjes

/-!
# The smoothed character estimate needed for Ankeny's bound

The Perron integral below uses the unnormalized triangular weight `x - n`.
An upper bound of order `x * √x * log q` for primitive nonprincipal characters
contradicts the untwisted lower bound of order `x²` if every small value is one.
-/

open Complex Finset MeasureTheory
open scoped ArithmeticFunction.vonMangoldt LSeries.notation
open ConjectureMachines.Semantics.Riemann.WeightedStieltjes

namespace CarryForward.Targets

/-- The open-strip statement from the archive's `src/Statements.lean`. -/
def DirichletLZerosOnLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2

/-- The primitive-character version of the archive's open-strip statement. -/
def PrimitiveDirichletLZerosOnLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
    ∀ s : ℂ, 0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2

/-- Removing Euler factors at imprimitive levels introduces no new zeros in the open strip. -/
theorem dirichletLZerosOnLine_iff_primitive :
    DirichletLZerosOnLine ↔ PrimitiveDirichletLZerosOnLine := by
  refine ⟨fun h q _ χ _ ↦ h q χ, ?_⟩
  intro h N _ χ s hs0 hs1 hz
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hs : s ≠ 1 := by rintro rfl; norm_num at hs1
  have he := DirichletCharacter.LFunction_changeLevel χ.conductor_dvd_level
    χ.primitiveCharacter (s := s) (Or.inr hs)
  rw [χ.changeLevel_primitiveCharacter, hz] at he
  apply h _ χ.primitiveCharacter χ.primitiveCharacter_isPrimitive s hs0 hs1
  refine (mul_eq_zero.mp he.symm).resolve_right (Finset.prod_ne_zero_iff.mpr ?_)
  intro p hp
  have hp1 : 1 < (p : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
  apply sub_ne_zero.mpr
  intro heq
  have hsmall : ‖χ.primitiveCharacter (p : ZMod χ.conductor) * (p : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul]
    have hn : ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := by
      simpa using Complex.norm_cpow_eq_rpow_re_of_pos (y := -s) (zero_lt_one.trans hp1)
    rw [hn]
    exact (mul_le_of_le_one_left (Real.rpow_nonneg (by positivity) _)
      (χ.primitiveCharacter.norm_le_one _)).trans_lt (Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith))
  rw [← heq, norm_one] at hsmall
  exact lt_irrefl _ hsmall

/-- Archive GRH implies nonvanishing in the entire open right half of the critical
strip and beyond, with the principal character at one excluded. -/
theorem LFunction_ne_zero_right_of_half (h : DirichletLZerosOnLine) {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 / 2 < s.re) (hp : χ ≠ 1 ∨ s ≠ 1) :
    χ.LFunction s ≠ 0 := by
  by_cases h1 : 1 ≤ s.re
  · exact χ.LFunction_ne_zero_of_one_le_re hp h1
  intro hz
  linarith [h N χ s (by linarith) (lt_of_not_ge h1) hz]

/-- The integrand whose vertical integral defines `characterPerron`. -/
noncomputable def characterIntegrand {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ) (s : ℂ) : ℂ :=
  (-deriv χ.LFunction s / χ.LFunction s) * smoothedPerronKernel x s

/-- Perron integral of the negative logarithmic derivative on the line of real part `c`. -/
noncomputable def characterPerron {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (x c : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ))⁻¹ * ∫ t : ℝ, characterIntegrand χ x ((c : ℂ) + (t : ℂ) * I)

/-- Exact smoothed Perron inversion for a Dirichlet character, including imprimitive ones. -/
theorem characterPerron_eq_sum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x c : ℝ} (hx : 0 < x) (hc : 1 < c) :
    characterPerron χ x c =
      ∑ n ∈ Icc 1 ⌊x⌋₊, χ (n : ZMod q) * (Λ n : ℂ) * ((x : ℂ) - n) := by
  have hs := χ.LSeriesSummable_twist_vonMangoldt (s := (c : ℂ)) (by simpa using hc)
  have h := smoothed_perron_LSeries hx (by linarith : 0 < c) hs
  refine Eq.trans ?_ h.symm
  unfold characterPerron
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  have ht : 1 < ((c : ℂ) + (t : ℂ) * I).re := by simpa using hc
  dsimp only [characterIntegrand]
  rw [χ.LSeries_twist_vonMangoldt_eq ht, χ.deriv_LFunction_eq_deriv_LSeries ht,
    χ.LFunction_eq_LSeries ht]

/-- Uniform right-edge bound, independent of both the modulus and the character. -/
theorem norm_character_logDeriv_two_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (t : ℝ) : ‖-deriv χ.LFunction (2 + (t : ℂ) * I) / χ.LFunction (2 + (t : ℂ) * I)‖ ≤ 2 := by
  let s : ℂ := 2 + (t : ℂ) * I
  have hs : 1 < s.re := by simp [s]
  change ‖-deriv χ.LFunction s / χ.LFunction s‖ ≤ 2
  rw [χ.deriv_LFunction_eq_deriv_LSeries hs, χ.LFunction_eq_LSeries hs,
    ← χ.LSeries_twist_vonMangoldt_eq hs]
  have ht := (χ.LSeriesSummable_twist_vonMangoldt hs).norm
  have hu := (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).norm
  refine (norm_tsum_le_tsum_norm ht).trans ((Summable.tsum_le_tsum ?_ ht hu).trans
    (tsum_norm_term_vonMangoldt_le_two t))
  intro n
  by_cases hn : n = 0
  · simp [LSeries.term, hn]
  · simp only [LSeries.term, ite_eq_right hn, Pi.mul_apply, norm_div, norm_mul]
    exact div_le_div_of_nonneg_right
      (mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)) (norm_nonneg _)

/-- The untwisted triangular sum has a quadratic lower bound with an absolute constant. -/
theorem psi1_lower_of_sixteen_le {x : ℝ} (hx : 16 ≤ x) : x ^ 2 / 16 ≤ psi1 x := by
  let m := ⌊x / 2⌋₊
  have hm : 7 ≤ m := (Nat.le_floor_iff (by positivity : 0 ≤ x / 2)).2 (by norm_num; linarith)
  have hmle : (m : ℝ) ≤ x / 2 := Nat.floor_le (by linarith)
  have hmlt : x / 2 < (m : ℝ) + 1 := Nat.lt_floor_add_one _
  have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hpsi := (Chebyshev.psi_ge_of_seven_le hm).trans (Chebyshev.psi_mono hmle)
  have hlow : x / 8 ≤ Chebyshev.psi (x / 2) := by
    nlinarith only [hpsi, hmlt, hx, mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg m)]
  have hpos : 0 ≤ psi1 (x / 2) :=
    intervalIntegral.integral_nonneg (by linarith : 1 ≤ x / 2) fun t _ ↦ Chebyshev.psi_nonneg t
  have hi := (mul_psi_le_psi1_sub_and_le (a := x / 2) (b := x) (by linarith)).1
  nlinarith only [hi, hpos, mul_le_mul_of_nonneg_left hlow (by linarith : 0 ≤ x / 2)]

/-- It suffices to bound primitive nonprincipal characters on the Perron line.
The same constant must work for all conductors and smoothing lengths. -/
def PrimitivePerronBound : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    χ.IsPrimitive → χ ≠ 1 → ∀ x : ℝ, 16 ≤ x →
      ‖characterPerron χ x 2‖ ≤ A * x * Real.sqrt x * Real.log q

/-- An absolute logarithmic-square bound for a positive witness against a nonprincipal character. -/
def AnkenyBound : Prop :=
  ∃ C : ℝ, ∀ (N : ℕ) [NeZero N], 2 < N → ∀ χ : DirichletCharacter ℂ N, χ ≠ 1 →
    ∃ a : ℕ, 0 < a ∧ (a : ℝ) ≤ C * Real.log N ^ 2 ∧ χ (a : ZMod N) ≠ 1

private theorem primitive_eq_one_of_eq_one {N a : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (h : χ (a : ZMod N) = 1) : χ.primitiveCharacter (a : ZMod χ.conductor) = 1 := by
  have hz : χ ((a : ℤ) : ZMod N) ≠ 0 := by simpa using h.trans_ne one_ne_zero
  have eq := χ.primitiveCharacter_apply_of_isCoprime ((χ.apply_ne_zero_iff _).1 hz)
  simpa using eq.trans (by simpa using h)

/-- A conductor-uniform primitive Perron bound gives Ankeny's bound at every modulus. -/
theorem ankenyBound_of_primitivePerronBound (h : PrimitivePerronBound) : AnkenyBound := by
  obtain ⟨A, hA, hbound⟩ := h
  let B := 16 * (A + 1)
  refine ⟨B ^ 2, fun N _ hN χ hχ ↦ ?_⟩
  have hn : 2 ≤ (N : ℝ) := by exact_mod_cast (by omega : 2 ≤ N)
  have hlog : 1 / 2 ≤ Real.log N :=
    (by linarith [Real.log_two_gt_d9] : (1 / 2 : ℝ) ≤ Real.log 2).trans (Real.log_le_log (by norm_num) hn)
  let y := B * Real.log N
  let x := y ^ 2
  have hy : 4 ≤ y := by dsimp [y, B]; nlinarith [mul_nonneg hA (by linarith : 0 ≤ Real.log N)]
  have hx : 16 ≤ x := by dsimp [x]; nlinarith
  have hx0 : 0 < x := by linarith
  have hscale : B ^ 2 * Real.log N ^ 2 = x := by dsimp [x, y]; ring
  rw [hscale]
  by_contra! hall
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hprim : χ.primitiveCharacter ≠ 1 := by
    intro he
    exact hχ (by rw [← χ.changeLevel_primitiveCharacter, he, DirichletCharacter.changeLevel_one])
  have hid : characterPerron χ.primitiveCharacter x 2 = (psi1 x : ℂ) := by
    rw [characterPerron_eq_sum _ hx0 (by norm_num), ofReal_psi1_eq_sum_Icc_vonMangoldt (by linarith)]
    apply sum_congr rfl
    intro n hn
    obtain ⟨hn1, hnx⟩ := mem_Icc.mp hn
    rw [primitive_eq_one_of_eq_one χ (hall n hn1 ((Nat.le_floor_iff hx0.le).1 hnx)), one_mul]
  have hb := hbound χ.conductor χ.primitiveCharacter χ.primitiveCharacter_isPrimitive hprim x hx
  rw [hid, Complex.norm_real, Real.norm_eq_abs, Real.sqrt_sq (by linarith : 0 ≤ y)] at hb
  have hc := Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero χ.conductor_ne_zero)
    (Nat.cast_le.mpr (Nat.le_of_dvd (by omega : 0 < N) χ.conductor_dvd_level) : (χ.conductor : ℝ) ≤ N)
  have hmain := (psi1_lower_of_sixteen_le hx).trans ((le_abs_self _).trans hb)
  have hb' : x / 16 ≤ A * y * Real.log N := by
    apply le_of_mul_le_mul_left (a := x) _ hx0
    nlinarith only [hmain, mul_le_mul_of_nonneg_left hc (show 0 ≤ A * x * y by positivity)]
  have hy' : y / 16 ≤ A * Real.log N := by
    apply le_of_mul_le_mul_left (a := y) _ (by linarith : 0 < y)
    dsimp only [x] at hb'
    linarith only [hb']
  dsimp [y, B] at hy'
  linarith

/-- Ankeny's cutoff transfers unchanged to strong Miller testing. -/
theorem miller_of_ankenyBound (h : AnkenyBound) :
    ∃ C : ℝ, ∀ n : ℕ, 2 < n → Odd n →
      (n.Prime ↔ ∀ a : ℕ, 2 ≤ a → a < n → (a : ℝ) ≤ C * Real.log n ^ 2 →
        IsStrongProbablePrime n a) := by
  obtain ⟨C, hC⟩ := h
  exact ⟨C, fun n hn ho ↦ miller_iff_of_character_witness hn _ (by intro _ χ; exact hC n hn χ)
    (isUnit_of_isStrongProbablePrime hn) (exists_proper_subgroup_of_composite hn ho)⟩

end CarryForward.Targets
