import NlsGge.GK38.MolnarCubicBoundary
import NlsGge.Spectral.TraceFormulaLowerOrder38
import NlsGge.Herglotz38.HerglotzMomentsE02_38

set_option autoImplicit false

open Filter Set MeasureTheory
open scoped Topology

namespace NlsGge.GK38.MolnarBounds38

open NlsGge.Pilot NlsGge.Schur NlsGge.SpectralFoundations

/-- Absolute first-moment integrability from the actual mass and second moment. -/
theorem actual_height_first_moment_integrable38 (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    Integrable (fun t : ℝ => t * actualGapHeightE02_38 u t) := by
  have hv := (actualGapHeight_integral_eq_normSq_E02_38 u hu).1
  have hv2 := actualMoment_integrable_of_sobolev38 1 le_rfl u (by simpa only [Nat.cast_one] using hu)
  refine (hv.add hv2).mono'
    (continuous_id.mul (continuous_actualGapHeightE02_38 u)).aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (actualGapHeightE02_38_nonneg u t)]
  have hfreq : |t| ≤ 1 + (2 * t) ^ 2 := by
    nlinarith [sq_abs t, sq_nonneg t, sq_nonneg (|t| - 1 / 2)]
  have h := mul_le_mul_of_nonneg_right hfreq (actualGapHeightE02_38_nonneg u t)
  simpa only [Pi.add_apply, add_mul, one_mul] using h

/-- The squared actual shift has a genuine Cauchy representation with signed density.
No nonnegative-density decomposition theorem is used. -/
theorem actual_shift_square_herglotz38 (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    ∀ z : ℂ, 0 < z.im →
      Integrable (fun t : ℝ =>
        ((2 * (actualQuasimomentumRealPartE02_38 u t - t) * actualGapHeightE02_38 u t : ℝ) : ℂ) /
          ((t : ℂ) - z)) ∧
      molnarShift38 u z ^ 2 = (1 / Real.pi : ℂ) *
        ∫ t : ℝ,
          ((2 * (actualQuasimomentumRealPartE02_38 u t - t) * actualGapHeightE02_38 u t : ℝ) : ℂ) /
            ((t : ℂ) - z) := by
  obtain ⟨C, hC, hdec⟩ := actualQuasimomentum_decay_E02_38 u hu
  have hsquare : ∀ w : ℂ, 0 ≤ w.im →
      ‖molnarShift38 u w ^ 2‖ ≤ C ^ 2 / Real.sqrt (1 + ‖w‖) := by
    intro w hw
    have hnorm : ‖molnarShift38 u w‖ ≤ C :=
      (hdec w hw).trans (div_le_self hC.le (sqrt_ge_one_E02_38 w))
    rw [norm_pow, pow_two]
    calc
      ‖molnarShift38 u w‖ * ‖molnarShift38 u w‖ ≤ C * (C / Real.sqrt (1 + ‖w‖)) :=
        mul_le_mul hnorm (hdec w hw) (norm_nonneg _) hC.le
      _ = _ := by ring
  have him : ∀ t : ℝ, (molnarShift38 u (t : ℂ) ^ 2).im =
      2 * (actualQuasimomentumRealPartE02_38 u t - t) * actualGapHeightE02_38 u t := by
    intro t
    simp only [pow_two, Complex.mul_im, molnarShift_boundary_re38, molnarShift_boundary_im38]
    ring
  have hrep := halfPlane_herglotz_of_decay_E02_38 (fun w => molnarShift38 u w ^ 2) (C ^ 2)
    ((molnarShift_differentiable38 u).pow 2)
    ((molnarShift_continuous38 u).pow 2) hsquare
  simpa only [him] using hrep

end NlsGge.GK38.MolnarBounds38
