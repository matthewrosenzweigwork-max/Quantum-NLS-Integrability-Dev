import NlsGge.Spectral.ActualInteractionDysonPairRecurrence32V1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace NlsGge.SpectralFoundations

/-- Exact off-diagonal entries of the original interaction coefficient. -/
theorem actualInteractionCoefficient_entries32 (U : ℝ → ℂ) (z : ℂ) (t : ℝ) :
    actualZsInteractionCoefficient32 U z t 0 1 =
      (Complex.I * U t) * Complex.exp (2 * (t : ℂ) * Complex.I * z) ∧
    actualZsInteractionCoefficient32 U z t 1 0 =
      (-Complex.I * star (U t)) * Complex.exp (-2 * (t : ℂ) * Complex.I * z) := by
  constructor
  · have h : actualZsInteractionCoefficient32 U z t 0 1 =
        Complex.exp (t • (Complex.I * z)) * (Complex.I * U t) /
          Complex.exp (t • (-(Complex.I * z))) := by
      simp [actualZsInteractionCoefficient32, actualZsInverseFreeWeight32,
        actualZsFreeRate32, zsCoefficientComplex]
    rw [h]
    calc
      _ = (Complex.I * U t) *
          Complex.exp ((t • (Complex.I * z)) - (t • (-(Complex.I * z)))) := by
            rw [Complex.exp_sub]
            ring
      _ = _ := by
        congr 1
        congr 1
        change (t : ℂ) * (Complex.I * z) - (t : ℂ) * (-(Complex.I * z)) =
          2 * (t : ℂ) * Complex.I * z
        ring
  · have h : actualZsInteractionCoefficient32 U z t 1 0 =
        Complex.exp (t • (-(Complex.I * z))) * (-Complex.I * star (U t)) /
          Complex.exp (t • (Complex.I * z)) := by
      simp [actualZsInteractionCoefficient32, actualZsInverseFreeWeight32,
        actualZsFreeRate32, zsCoefficientComplex]
    rw [h]
    calc
      _ = (-Complex.I * star (U t)) *
          Complex.exp ((t • (-(Complex.I * z))) - (t • (Complex.I * z))) := by
            rw [Complex.exp_sub]
            ring
      _ = _ := by
        congr 1
        congr 1
        change (t : ℂ) * (-(Complex.I * z)) - (t : ℂ) * (Complex.I * z) =
          -2 * (t : ℂ) * Complex.I * z
        ring

/-- The 00 pair has the decaying phase in the upper half-plane; the 11 pair
has the opposite phase. These exact complex identities do not assert that
the potential product is real. -/
theorem actualInteractionPairKernel32 (U : ℝ → ℂ) (z : ℂ) (s r : ℝ) :
    actualZsInteractionCoefficient32 U z s 0 1 *
        actualZsInteractionCoefficient32 U z r 1 0 =
      U s * star (U r) * Complex.exp (2 * Complex.I * z * ((s-r : ℝ) : ℂ)) ∧
    actualZsInteractionCoefficient32 U z s 1 0 *
        actualZsInteractionCoefficient32 U z r 0 1 =
      star (U s) * U r * Complex.exp (-2 * Complex.I * z * ((s-r : ℝ) : ℂ)) := by
  have hs := actualInteractionCoefficient_entries32 U z s
  have hr := actualInteractionCoefficient_entries32 U z r
  constructor
  · rw [hs.1, hr.2]
    calc
      _ = -(Complex.I * Complex.I) * (U s * star (U r)) *
          (Complex.exp (2 * (s : ℂ) * Complex.I * z) *
            Complex.exp (-2 * (r : ℂ) * Complex.I * z)) := by ring
      _ = _ := by
        simp only [Complex.I_mul_I, neg_neg, one_mul, ← Complex.exp_add]
        congr 1
        congr 1
        push_cast
        ring
  · rw [hs.2, hr.1]
    calc
      _ = -(Complex.I * Complex.I) * (star (U s) * U r) *
          (Complex.exp (-2 * (s : ℂ) * Complex.I * z) *
            Complex.exp (2 * (r : ℂ) * Complex.I * z)) := by ring
      _ = _ := by
        simp only [Complex.I_mul_I, neg_neg, one_mul, ← Complex.exp_add]
        congr 1
        congr 1
        push_cast
        ring

/-- Exact pair norms, retaining the opposite exponential signs. In
particular only the 00 pair is bounded by the decaying triangle kernel. -/
theorem actualInteractionPairKernel_norm32 (U : ℝ → ℂ) (z : ℂ) (s r : ℝ) :
    ‖actualZsInteractionCoefficient32 U z s 0 1 *
        actualZsInteractionCoefficient32 U z r 1 0‖ =
      ‖U s‖ * ‖U r‖ * Real.exp (-2 * z.im * (s-r)) ∧
    ‖actualZsInteractionCoefficient32 U z s 1 0 *
        actualZsInteractionCoefficient32 U z r 0 1‖ =
      ‖U s‖ * ‖U r‖ * Real.exp (2 * z.im * (s-r)) := by
  have h := actualInteractionPairKernel32 U z s r
  constructor
  · rw [h.1]
    simp only [norm_mul, norm_star, Complex.norm_exp]
    congr 1
    congr 1
    simp [Complex.mul_re, Complex.mul_im]
  · rw [h.2]
    simp only [norm_mul, norm_star, Complex.norm_exp]
    congr 1
    congr 1
    simp [Complex.mul_re, Complex.mul_im]

end NlsGge.SpectralFoundations
end
