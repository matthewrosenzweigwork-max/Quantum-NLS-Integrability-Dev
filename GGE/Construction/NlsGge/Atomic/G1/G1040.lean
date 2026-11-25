import NlsGge.Spectral.ActualQuasimomentumContinuityE02_38
import Mathlib.Tactic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace NlsGge.Atomic.G1

open NlsGge.SpectralFoundations

/-- Away from every vacuum disc of radius `π/4`, the sine grows strongly enough
to dominate the exponential of the imaginary part. -/
theorem sin_lower_outside_discs (z : ℂ)
    (h : ∀ n : ℤ, Real.pi / 4 ≤ ‖z - (n : ℂ) * Real.pi‖) :
    Real.exp |z.im| < 4 * ‖Complex.sin z‖ := by
  let m : ℤ := round (z.re / Real.pi)
  let r : ℝ := z.re - m * Real.pi
  let x : ℝ := |z.im|
  have hπ : 0 < Real.pi := Real.pi_pos
  have hrabs : |r| ≤ Real.pi / 2 := by
    have hr := abs_sub_round (z.re / Real.pi)
    have hrepr : r = (z.re / Real.pi - m) * Real.pi := by
      simp [r, m]
      field_simp
    rw [hrepr, abs_mul, abs_of_pos hπ]
    nlinarith
  have hzre : (z - (m : ℂ) * Real.pi).re = r := by
    simp [r]
  have hzim : (z - (m : ℂ) * Real.pi).im = z.im := by simp
  have hdisc := h m
  have hdiscSq : (Real.pi / 4) ^ 2 ≤ ‖z - (m : ℂ) * Real.pi‖ ^ 2 := by
    nlinarith [norm_nonneg (z - (m : ℂ) * Real.pi)]
  have hdistSq : (Real.pi / 4) ^ 2 ≤ r ^ 2 + x ^ 2 := by
    have hs := Complex.sq_norm (z - (m : ℂ) * Real.pi)
    rw [Complex.normSq_apply, hzre, hzim] at hs
    have hx2 : z.im ^ 2 = x ^ 2 := by simp [x]
    nlinarith [hdiscSq, hs, hx2]
  have hsinShift : ‖Complex.sin (z - (m : ℂ) * Real.pi)‖ = ‖Complex.sin z‖ :=
    norm_sin_sub_int_mul_pi_E02_38 z m
  have hsinId := norm_sin_sq_E02_38 (z - (m : ℂ) * Real.pi)
  rw [hsinShift, hzre, hzim] at hsinId
  have hsinhAbs : Real.sinh (z.im) ^ 2 = Real.sinh x ^ 2 := by
    rcases le_total 0 (z.im) with hpos | hneg
    · simp [x, abs_of_nonneg hpos]
    · have : z.im = -x := by simp [x, abs_of_nonpos hneg]
      rw [this, Real.sinh_neg, neg_sq]
  rw [hsinhAbs] at hsinId
  have hx0 : 0 ≤ x := abs_nonneg _
  by_cases hsmall : x ≤ 1 / 2
  · have hrpi : Real.pi / 6 ≤ |r| := by
      have hsquare : (Real.pi / 6) ^ 2 ≤ r ^ 2 := by
        have hπ3 := Real.pi_gt_three
        nlinarith [sq_nonneg x, sq_nonneg r]
      by_contra hnot
      have habs : |r| < Real.pi / 6 := lt_of_not_ge hnot
      have hlt : r ^ 2 < (Real.pi / 6) ^ 2 := by
        rw [← sq_abs r]
        exact (sq_lt_sq₀ (abs_nonneg r) (by positivity)).2 habs
      linarith
    have hsinAbsSq : Real.sin r ^ 2 = Real.sin |r| ^ 2 := by
      rcases le_total 0 r with hr | hr
      · simp [abs_of_nonneg hr]
      · simp [abs_of_nonpos hr, Real.sin_neg]
    have hsinLower : (1 / 2 : ℝ) ≤ Real.sin |r| := by
      have hmono := Real.sin_le_sin_of_le_of_le_pi_div_two
        (by linarith [abs_nonneg r]) (by linarith [hrabs]) hrpi
      simpa using hmono
    have hnormLower : (1 / 2 : ℝ) ≤ ‖Complex.sin z‖ := by
      have hsinNonneg : 0 ≤ Real.sin r ^ 2 + Real.sinh x ^ 2 := by positivity
      have hsq : (1 / 2 : ℝ) ^ 2 ≤ ‖Complex.sin z‖ ^ 2 := by
        rw [hsinId]
        rw [hsinAbsSq]
        have hsinSq : (1 / 2 : ℝ) ^ 2 ≤ Real.sin |r| ^ 2 := by
          nlinarith [sq_nonneg (Real.sin |r|)]
        nlinarith
      nlinarith [norm_nonneg (Complex.sin z)]
    have hexpHalf : Real.exp (1 / 2 : ℝ) < 2 := by
      have hsquare : Real.exp (1 / 2 : ℝ) ^ 2 = Real.exp 1 := by
        rw [pow_two, ← Real.exp_add]
        norm_num
      have hpos := Real.exp_pos (1 / 2 : ℝ)
      nlinarith [Real.exp_one_lt_three]
    have hexp : Real.exp x ≤ Real.exp (1 / 2 : ℝ) :=
      Real.exp_le_exp.mpr hsmall
    simpa [x] using (show Real.exp x < 4 * ‖Complex.sin z‖ by linarith)
  · have hxlarge : (1 / 2 : ℝ) < x := lt_of_not_ge hsmall
    have hsinhNonneg : 0 ≤ Real.sinh x :=
      le_trans hx0 (Real.self_le_sinh_iff.mpr hx0)
    have hnormSq : Real.sinh x ^ 2 ≤ ‖Complex.sin z‖ ^ 2 := by
      rw [hsinId]
      nlinarith [sq_nonneg (Real.sin r)]
    have hnormLower : Real.sinh x ≤ ‖Complex.sin z‖ := by
      nlinarith [norm_nonneg (Complex.sin z)]
    have hexpCompare : 2 * Real.exp (-x) < Real.exp x := by
      have harg : (1 : ℝ) < 2 * x := by linarith
      have hmono : Real.exp 1 < Real.exp (2 * x) := Real.exp_lt_exp.mpr harg
      have htwo : (2 : ℝ) < Real.exp (2 * x) := lt_trans Real.exp_one_gt_two hmono
      have heq : Real.exp (2 * x) * Real.exp (-x) = Real.exp x := by
        rw [← Real.exp_add]
        ring_nf
      have hmul := mul_lt_mul_of_pos_right htwo (Real.exp_pos (-x))
      rw [heq] at hmul
      nlinarith [Real.exp_pos (-x)]
    have hsinhFormula := Real.sinh_eq x
    have hexpSine : Real.exp x < 4 * Real.sinh x := by
      rw [hsinhFormula]
      nlinarith [Real.exp_pos x, Real.exp_pos (-x), hexpCompare]
    simpa [x] using
      (lt_of_lt_of_le hexpSine (mul_le_mul_of_nonneg_left hnormLower (by norm_num)))

end NlsGge.Atomic.G1
