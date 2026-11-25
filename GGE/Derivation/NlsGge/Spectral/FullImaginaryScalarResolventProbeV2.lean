import Mathlib.Analysis.Complex.Norm

set_option autoImplicit false
noncomputable section

namespace NlsGge.Pilot.FullImaginaryScalarResolventProbeV2

/-- The squared modulus of the full imaginary-shift denominator.  The formula
includes `a = 0`; in particular, this API does not remove a resonant mode. -/
theorem normSq_imaginary_sub_real (y a : ℝ) :
    Complex.normSq (Complex.I * (y : ℂ) - (a : ℂ)) = y ^ 2 + a ^ 2 := by
  rw [Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- The scalar denominator is nonzero for every strictly positive imaginary
shift, uniformly in the real mode parameter. -/
theorem imaginary_sub_real_ne_zero {y a : ℝ} (hy : 0 < y) :
    Complex.I * (y : ℂ) - (a : ℂ) ≠ 0 := by
  apply (Complex.normSq_pos).1
  rw [normSq_imaginary_sub_real]
  positivity

/-- Exact inverse squared-modulus identity for every real mode, including zero. -/
theorem normSq_imaginary_sub_real_inv (y a : ℝ) :
    Complex.normSq ((Complex.I * (y : ℂ) - (a : ℂ))⁻¹) =
      (y ^ 2 + a ^ 2)⁻¹ := by
  rw [Complex.normSq_inv, normSq_imaginary_sub_real]

/-- The unweighted resolvent coefficient has squared modulus at most `y⁻²`.
This form is convenient for summing over signed Fourier modes. -/
theorem normSq_imaginary_sub_real_inv_le (y a : ℝ) (hy : 0 < y) :
    Complex.normSq ((Complex.I * (y : ℂ) - (a : ℂ))⁻¹) ≤ (y ^ 2)⁻¹ := by
  rw [normSq_imaginary_sub_real_inv]
  simpa only [one_div] using
    (one_div_le_one_div_of_le (by positivity : 0 < y ^ 2)
      (show y ^ 2 ≤ y ^ 2 + a ^ 2 by nlinarith [sq_nonneg a]))

/-- The weighted multiplier is contractive in modulus: the diagonal factor
`a` is paired with the same full imaginary-shift inverse at every mode. -/
theorem weighted_imaginary_resolvent_norm_le_one {y a : ℝ} (hy : 0 < y) :
    ‖(a : ℂ) * (Complex.I * (y : ℂ) - (a : ℂ))⁻¹‖ ≤ 1 := by
  have hsq : Complex.normSq ((a : ℂ) *
      (Complex.I * (y : ℂ) - (a : ℂ))⁻¹) ≤ 1 := by
    rw [Complex.normSq_mul, Complex.normSq_ofReal,
      normSq_imaginary_sub_real_inv]
    rw [← div_eq_mul_inv]
    apply (div_le_one₀ (by positivity : 0 < y ^ 2 + a ^ 2)).2
    nlinarith [sq_nonneg a]
  have hnorm : Complex.normSq ((a : ℂ) *
      (Complex.I * (y : ℂ) - (a : ℂ))⁻¹) =
        ‖(a : ℂ) * (Complex.I * (y : ℂ) - (a : ℂ))⁻¹‖ ^ 2 :=
    Complex.normSq_eq_norm_sq _
  rw [hnorm] at hsq
  nlinarith [sq_nonneg (‖(a : ℂ) *
    (Complex.I * (y : ℂ) - (a : ℂ))⁻¹‖ - 1)]

end NlsGge.Pilot.FullImaginaryScalarResolventProbeV2
