import NlsGge.GK38.MolnarSignedSquare

set_option autoImplicit false

open Filter Set MeasureTheory
open scoped Topology

namespace NlsGge.GK38.MolnarBounds38

open NlsGge.Pilot NlsGge.Schur NlsGge.SpectralFoundations

/-- Real part of an absolutely integrable Cauchy kernel; its real density may have either sign. -/
theorem signed_cauchy_axis_re38 (g : ℝ → ℝ) (y : ℝ) (hy : 1 ≤ y)
    (hi : Integrable (fun t : ℝ => (g t : ℂ) / ((t : ℂ) - Complex.I * (y : ℂ)))) :
    (∫ t : ℝ, (g t : ℂ) / ((t : ℂ) - Complex.I * (y : ℂ))).re =
      ∫ t : ℝ, g t * (t / (t ^ 2 + y ^ 2)) := by
  refine (integral_re hi).symm.trans ?_
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  change ((g t : ℂ) / ((t : ℂ) - Complex.I * (y : ℂ))).re =
    g t * (t / (t ^ 2 + y ^ 2))
  simpa only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, zero_mul, one_mul, mul_zero, sub_zero, add_zero]
    using congrArg Complex.re (hm38_pt (g t) t y hy)

/-- Imaginary part of an absolutely integrable Cauchy kernel, without a positivity hypothesis. -/
theorem signed_cauchy_axis_im38 (g : ℝ → ℝ) (y : ℝ) (hy : 1 ≤ y)
    (hi : Integrable (fun t : ℝ => (g t : ℂ) / ((t : ℂ) - Complex.I * (y : ℂ)))) :
    (∫ t : ℝ, (g t : ℂ) / ((t : ℂ) - Complex.I * (y : ℂ))).im =
      ∫ t : ℝ, g t * (y / (t ^ 2 + y ^ 2)) := by
  refine (integral_im hi).symm.trans ?_
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  change ((g t : ℂ) / ((t : ℂ) - Complex.I * (y : ℂ))).im =
    g t * (y / (t ^ 2 + y ^ 2))
  simpa only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, zero_mul, one_mul, mul_zero, zero_add, add_zero]
    using congrArg Complex.im (hm38_pt (g t) t y hy)

theorem molnarShift_upper38 (u : PhysicalL2) (z : ℂ) (hz : 0 < z.im) :
    molnarShift38 u z = actualQuasimomentumE02_38 u z - z := by
  have hk := isActualQuasimomentumBranch_actualQuasimomentumE02_38 u
  have hext := extendFrom_extends hk.1.continuousOn z hz
  unfold molnarShift38
  rw [hext]

/-- The original actual Herglotz formula expressed in the concrete shift used for the cube. -/
theorem actual_shift_herglotz38 (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) (z : ℂ) (hz : 0 < z.im) :
    Integrable (fun t : ℝ => (actualGapHeightE02_38 u t : ℂ) / ((t : ℂ) - z)) ∧
    molnarShift38 u z = (1 / Real.pi : ℂ) *
      ∫ t : ℝ, (actualGapHeightE02_38 u t : ℂ) / ((t : ℂ) - z) := by
  obtain ⟨hi, heq⟩ := actualQuasimomentum_herglotz_E02_38 u hu z hz
  refine ⟨hi, ?_⟩
  rw [molnarShift_upper38 u z hz, heq]
  ring

end NlsGge.GK38.MolnarBounds38
