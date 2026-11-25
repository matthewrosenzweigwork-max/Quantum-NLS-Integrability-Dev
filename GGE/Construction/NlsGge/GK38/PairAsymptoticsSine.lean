import NlsGge.GK38.Lib.RoucheProbe
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Algebra.Order.Floor.Ring

/-!
# F5: the sine lower bound off the lattice discs

Source: Grébert–Kappeler, Appendix F, Lemma F.2. The proof uses the accepted
identity `‖sin(x+iy)‖² = sin² x + sinh² y`. For `|y| ≥ π/8`, the hyperbolic
term controls `exp |y|`. Otherwise a nearest lattice point gives a real
displacement between `π/8` and `π/2`, and the real sine chord bound applies.
The disc boundaries are included, and the constant is absolute.
-/

set_option autoImplicit false

namespace NlsGge.GK38

noncomputable section

/-- A real component of the sine norm identity. -/
theorem abs_real_sin_le_complex_sin38 (z : ℂ) : |Real.sin z.re| ≤ ‖Complex.sin z‖ := by
  have h := Lib.normSq_sin' z
  rw [← Complex.sq_norm] at h
  nlinarith [sq_nonneg (Real.sinh z.im), sq_abs (Real.sin z.re),
    abs_nonneg (Real.sin z.re), norm_nonneg (Complex.sin z)]

/-- The hyperbolic component controls the sine norm for either sign of the imaginary part. -/
theorem sinh_abs_im_le_complex_sin38 (z : ℂ) : Real.sinh |z.im| ≤ ‖Complex.sin z‖ := by
  rw [← Real.abs_sinh]
  have h := Lib.normSq_sin' z
  rw [← Complex.sq_norm] at h
  nlinarith [sq_nonneg (Real.sin z.re), sq_abs (Real.sinh z.im),
    abs_nonneg (Real.sinh z.im), norm_nonneg (Complex.sin z)]

/-- Above height `π/8`, the exponential is bounded by a fixed multiple of the hyperbolic sine. -/
theorem exp_le_sinh_of_pi_eighth_le38 {t : ℝ} (ht : Real.pi / 8 ≤ t) :
    Real.exp t ≤ (2 + 8 / Real.pi) * Real.sinh t := by
  have ht0 : 0 ≤ t := by linarith [Real.pi_pos]
  have hst : t ≤ Real.sinh t := Real.self_le_sinh_iff.mpr ht0
  have he : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hidentity : Real.exp t = 2 * Real.sinh t + Real.exp (-t) := by
    rw [Real.sinh_eq]; ring
  have hunit : 1 ≤ (8 / Real.pi) * Real.sinh t := by
    have hp : 0 < Real.pi := Real.pi_pos
    have hmul := mul_le_mul_of_nonneg_left (ht.trans hst) (by positivity : 0 ≤ 8 / Real.pi)
    have hcancel : (8 / Real.pi) * (Real.pi / 8) = 1 := by field_simp
    rwa [hcancel] at hmul
  rw [hidentity]
  nlinarith

/-- Every real point is within `π/2` of some integral lattice point. -/
theorem exists_nearest_pi_lattice38 (x : ℝ) :
    ∃ n : ℤ, |x - (n : ℝ) * Real.pi| ≤ Real.pi / 2 := by
  refine ⟨⌊x / Real.pi + 1 / 2⌋, ?_⟩
  have hlo := Int.floor_le (x / Real.pi + 1 / 2)
  have hhi := Int.lt_floor_add_one (x / Real.pi + 1 / 2)
  have hp := Real.pi_pos
  have h1 := mul_le_mul_of_nonneg_right hlo hp.le
  have h2 := mul_lt_mul_of_pos_right hhi hp
  rw [add_mul, div_mul_cancel₀ x hp.ne'] at h1 h2
  rw [abs_le]
  constructor <;> linarith

/-- The absolute real sine is unchanged by an integral lattice translation. -/
theorem abs_sin_sub_int_pi38 (x : ℝ) (n : ℤ) :
    |Real.sin (x - (n : ℝ) * Real.pi)| = |Real.sin x| := by
  rw [Real.sin_sub_int_mul_pi, abs_mul]
  simp

/-- In the low-height strip, being off every disc forces a uniform positive sine norm. -/
theorem quarter_le_sin_off_discs_low_im38 (z : ℂ)
    (hdisc : ∀ n : ℤ, Real.pi / 4 ≤ ‖z - (n : ℂ) * (Real.pi : ℂ)‖)
    (him : |z.im| ≤ Real.pi / 8) : 1 / 4 ≤ ‖Complex.sin z‖ := by
  obtain ⟨n, hn⟩ := exists_nearest_pi_lattice38 z.re
  have hnorm := Complex.norm_le_abs_re_add_abs_im (z - (n : ℂ) * (Real.pi : ℂ))
  have hnorm' : ‖z - (n : ℂ) * (Real.pi : ℂ)‖ ≤
      |z.re - (n : ℝ) * Real.pi| + |z.im| := by simpa using hnorm
  have hsmall : Real.pi / 8 ≤ |z.re - (n : ℝ) * Real.pi| := by
    linarith [hdisc n]
  have hchord := Real.mul_abs_le_abs_sin hn
  rw [abs_sin_sub_int_pi38] at hchord
  have hquarter : (2 / Real.pi) * (Real.pi / 8) = (1 / 4 : ℝ) := by
    field_simp
    norm_num
  calc (1 / 4 : ℝ) = (2 / Real.pi) * (Real.pi / 8) := hquarter.symm
    _ ≤ (2 / Real.pi) * |z.re - (n : ℝ) * Real.pi| :=
      mul_le_mul_of_nonneg_left hsmall (by positivity)
    _ ≤ |Real.sin z.re| := hchord
    _ ≤ ‖Complex.sin z‖ := abs_real_sin_le_complex_sin38 z

/-- An explicit absolute constant valid in both height regimes. -/
def sineOffDiscsConstant38 : ℝ :=
  max (4 * Real.exp (Real.pi / 8)) (2 + 8 / Real.pi)

theorem sineOffDiscsConstant38_pos : 0 < sineOffDiscsConstant38 :=
  lt_of_lt_of_le (by positivity) (le_max_left _ _)

/-- The sine controls the exponential off the open discs of radius `π/4`, including their boundaries. -/
theorem sine_off_discs_lower_bound38 (z : ℂ)
    (hdisc : ∀ n : ℤ, Real.pi / 4 ≤ ‖z - (n : ℂ) * (Real.pi : ℂ)‖) :
    Real.exp |z.im| ≤ sineOffDiscsConstant38 * ‖Complex.sin z‖ := by
  by_cases him : |z.im| ≤ Real.pi / 8
  · have hsin := quarter_le_sin_off_discs_low_im38 z hdisc him
    have he := Real.exp_le_exp.mpr him
    have hpos := Real.exp_pos (Real.pi / 8)
    calc Real.exp |z.im| ≤ Real.exp (Real.pi / 8) := he
      _ ≤ (4 * Real.exp (Real.pi / 8)) * ‖Complex.sin z‖ := by nlinarith
      _ ≤ sineOffDiscsConstant38 * ‖Complex.sin z‖ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  · have ht : Real.pi / 8 ≤ |z.im| := (lt_of_not_ge him).le
    have hs := sinh_abs_im_le_complex_sin38 z
    calc Real.exp |z.im| ≤ (2 + 8 / Real.pi) * Real.sinh |z.im| :=
        exp_le_sinh_of_pi_eighth_le38 ht
      _ ≤ (2 + 8 / Real.pi) * ‖Complex.sin z‖ :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      _ ≤ sineOffDiscsConstant38 * ‖Complex.sin z‖ :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)

/-- F5's absolute uniform lower-bound API (book Appendix F, Lemma F.2). -/
theorem exists_sine_off_discs_lower_bound38 :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ,
      (∀ n : ℤ, Real.pi / 4 ≤ ‖z - (n : ℂ) * (Real.pi : ℂ)‖) →
        Real.exp |z.im| ≤ C * ‖Complex.sin z‖ :=
  ⟨sineOffDiscsConstant38, sineOffDiscsConstant38_pos, sine_off_discs_lower_bound38⟩

/-! ## Regression probes -/

/-- Every real point `nπ+π/4` is on one disc boundary and outside all other open discs. -/
theorem sine_probe_real_boundary_off_discs38 (n m : ℤ) :
    Real.pi / 4 ≤ ‖((n : ℂ) * (Real.pi : ℂ) + (Real.pi : ℂ) / 4) -
      (m : ℂ) * (Real.pi : ℂ)‖ := by
  have he : ((n : ℂ) * (Real.pi : ℂ) + (Real.pi : ℂ) / 4) -
      (m : ℂ) * (Real.pi : ℂ) =
      (((n : ℝ) * Real.pi + Real.pi / 4 - (m : ℝ) * Real.pi : ℝ) : ℂ) := by
    push_cast
    ring
  rw [he, Complex.norm_real, Real.norm_eq_abs]
  rcases le_or_gt m n with hmn | hmn
  · have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn
    have hp := mul_le_mul_of_nonneg_right hmnR Real.pi_pos.le
    exact (by linarith : Real.pi / 4 ≤ (n : ℝ) * Real.pi + Real.pi / 4 - m * Real.pi).trans
      (le_abs_self _)
  · have hmnR : (n : ℝ) + 1 ≤ m := by exact_mod_cast (by omega : n + 1 ≤ m)
    have hp := mul_le_mul_of_nonneg_right hmnR Real.pi_pos.le
    exact (by nlinarith [Real.pi_pos] : Real.pi / 4 ≤
      -((n : ℝ) * Real.pi + Real.pi / 4 - m * Real.pi)).trans (neg_le_abs _)

/-- Boundary regression at every lattice translate, including negative labels. -/
theorem sine_probe_real_boundary38 (n : ℤ) :
    1 ≤ sineOffDiscsConstant38 *
      ‖Complex.sin ((n : ℂ) * (Real.pi : ℂ) + (Real.pi : ℂ) / 4)‖ := by
  simpa using sine_off_discs_lower_bound38
    ((n : ℂ) * (Real.pi : ℂ) + (Real.pi : ℂ) / 4)
    (sine_probe_real_boundary_off_discs38 n)

/-- Independent closed-form check at the boundary point `π/4`. -/
theorem sine_probe_pi_quarter_norm38 :
    ‖Complex.sin ((Real.pi : ℂ) / 4)‖ = Real.sqrt 2 / 2 := by
  have he : (Real.pi : ℂ) / 4 = ((Real.pi / 4 : ℝ) : ℂ) := by push_cast; rfl
  rw [he, ← Complex.ofReal_sin, Complex.norm_real, Real.norm_eq_abs,
    Real.sin_pi_div_four, abs_of_nonneg (by positivity)]

/-- Both imaginary half-axes are covered, including the boundary height `π/4`. -/
theorem sine_probe_imaginary38 (y : ℝ) (hy : Real.pi / 4 ≤ |y|) :
    Real.exp |y| ≤ sineOffDiscsConstant38 * ‖Complex.sin (Complex.I * (y : ℂ))‖ := by
  have hdisc : ∀ n : ℤ, Real.pi / 4 ≤
      ‖Complex.I * (y : ℂ) - (n : ℂ) * (Real.pi : ℂ)‖ := by
    intro n
    have h := Complex.abs_im_le_norm (Complex.I * (y : ℂ) - (n : ℂ) * (Real.pi : ℂ))
    exact hy.trans (by simpa using h)
  simpa using sine_off_discs_lower_bound38 (Complex.I * (y : ℂ)) hdisc

end
end NlsGge.GK38
