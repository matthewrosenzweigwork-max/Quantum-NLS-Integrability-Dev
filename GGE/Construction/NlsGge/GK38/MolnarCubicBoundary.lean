import NlsGge.GK38.MolnarCubicCauchy
import NlsGge.Spectral.ActualActionSumE02_38

set_option autoImplicit false

open Filter Set MeasureTheory
open scoped Topology

namespace NlsGge.GK38.MolnarBounds38

open NlsGge.Pilot NlsGge.Schur NlsGge.SpectralFoundations

theorem molnarShift_boundary_im38 (u : PhysicalL2) (t : ℝ) :
    (molnarShift38 u (t : ℂ)).im = actualGapHeightE02_38 u t := by
  have h := boundaryLimit_im_E02_38 u t _ (tendsto_actualQuasimomentumBoundaryE02_38 u t)
  simp only [molnarShift_boundary38, Complex.sub_im, Complex.ofReal_im, sub_zero]
  exact h

theorem molnarShift_boundary_re38 (u : PhysicalL2) (t : ℝ) :
    (molnarShift38 u (t : ℂ)).re = actualQuasimomentumRealPartE02_38 u t - t := rfl

theorem actual_shift_height_uniform_bound38 (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      |actualQuasimomentumRealPartE02_38 u t - t| ≤ C ∧ actualGapHeightE02_38 u t ≤ C := by
  obtain ⟨C, hC, hdec⟩ := actualQuasimomentum_decay_E02_38 u hu
  refine ⟨C, hC, fun t => ?_⟩
  have hbound : ‖molnarShift38 u (t : ℂ)‖ ≤ C :=
    (hdec (t : ℂ) (by simp)).trans (div_le_self hC.le (sqrt_ge_one_E02_38 (t : ℂ)))
  constructor
  · rw [← molnarShift_boundary_re38]
    exact (Complex.abs_re_le_norm _).trans hbound
  · rw [← molnarShift_boundary_im38]
    exact (le_abs_self _).trans ((Complex.abs_im_le_norm _).trans hbound)

/-- Cubic real components are integrable individually before taking the imaginary-part identity. -/
theorem actual_shift_square_height38 (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    Integrable (fun t : ℝ => actualGapHeightE02_38 u t ^ 3) ∧
    Integrable (fun t : ℝ =>
      (actualQuasimomentumRealPartE02_38 u t - t) ^ 2 * actualGapHeightE02_38 u t) ∧
    (∫ t : ℝ,
      (actualQuasimomentumRealPartE02_38 u t - t) ^ 2 * actualGapHeightE02_38 u t) =
      (1 / 3 : ℝ) * ∫ t : ℝ, actualGapHeightE02_38 u t ^ 3 := by
  obtain ⟨C, hC, hbound⟩ := actual_shift_height_uniform_bound38 u hu
  have hv := continuous_actualGapHeightE02_38 u
  have hv0 := actualGapHeightE02_38_nonneg u
  have hvi := (actualGapHeight_integral_eq_normSq_E02_38 u hu).1
  have hdom := hvi.const_mul (C ^ 2)
  have hcube : Integrable (fun t : ℝ => actualGapHeightE02_38 u t ^ 3) := by
    refine hdom.mono' (hv.pow 3).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hv0 t) 3)]
    calc
      actualGapHeightE02_38 u t ^ 3 =
          actualGapHeightE02_38 u t ^ 2 * actualGapHeightE02_38 u t := by ring
      _ ≤ C ^ 2 * actualGapHeightE02_38 u t :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hv0 t) (hbound t).2 2) (hv0 t)
  have ha := (continuous_actualQuasimomentumRealPartE02_38 u).sub continuous_id
  have hsq : Integrable (fun t : ℝ =>
      (actualQuasimomentumRealPartE02_38 u t - t) ^ 2 * actualGapHeightE02_38 u t) := by
    refine hdom.mono' ((ha.pow 2).mul hv).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (hv0 t))]
    apply mul_le_mul_of_nonneg_right _ (hv0 t)
    have h := pow_le_pow_left₀ (abs_nonneg (actualQuasimomentumRealPartE02_38 u t - t))
      (hbound t).1 2
    simpa only [sq_abs] using h
  have hcomplex := actual_quasimomentum_shift_cube_integral38 u hu
  have hpoly : ∀ t : ℝ,
      ((actualQuasimomentumBoundaryE02_38 u t - (t : ℂ)) ^ 3).im =
        3 * ((actualQuasimomentumRealPartE02_38 u t - t) ^ 2 * actualGapHeightE02_38 u t) -
          actualGapHeightE02_38 u t ^ 3 := by
    intro t
    have him := boundaryLimit_im_E02_38 u t _ (tendsto_actualQuasimomentumBoundaryE02_38 u t)
    simp only [pow_succ, pow_zero, mul_one, Complex.mul_re, Complex.mul_im,
      Complex.one_re, Complex.one_im, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, sub_zero]
    simp only [him]
    change _ = 3 * (((actualQuasimomentumBoundaryE02_38 u t).re - t) ^ 2 *
      actualGapHeightE02_38 u t) - actualGapHeightE02_38 u t ^ 3
    ring
  have hzero : (∫ t : ℝ,
      3 * ((actualQuasimomentumRealPartE02_38 u t - t) ^ 2 * actualGapHeightE02_38 u t) -
        actualGapHeightE02_38 u t ^ 3) = 0 := by
    calc
      _ = ∫ t : ℝ, ((actualQuasimomentumBoundaryE02_38 u t - (t : ℂ)) ^ 3).im :=
        integral_congr_ae (Eventually.of_forall fun t => (hpoly t).symm)
      _ = (∫ t : ℝ, (actualQuasimomentumBoundaryE02_38 u t - (t : ℂ)) ^ 3).im :=
        integral_im hcomplex.1
      _ = 0 := by rw [hcomplex.2]; rfl
  rw [integral_sub (hsq.const_mul 3) hcube, integral_const_mul] at hzero
  exact ⟨hcube, hsq, by linarith⟩

end NlsGge.GK38.MolnarBounds38
