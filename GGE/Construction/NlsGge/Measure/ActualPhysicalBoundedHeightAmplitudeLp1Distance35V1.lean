import NlsGge.Measure.ActualPhysicalBoundedHeightAmplitudeLp1Classes35V2
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace NlsGge.SpectralFoundations
open NlsGge.Pilot NlsGge.Schur NlsGge.Analysis

/-- The actual L¹-class distance in the 00 channel is exactly the full-line
integral distance of the source amplitudes. -/
theorem actualPhysicalHeightAmplitude00Lp1_35V2_dist_eq_integral
    (u : PhysicalL2) (Y₀ : ℝ) (hY₀ : 0 ≤ Y₀)
    (p q : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) Y₀) :
    dist (actualPhysicalHeightAmplitude00Lp1_35V2 u Y₀ hY₀ p)
      (actualPhysicalHeightAmplitude00Lp1_35V2 u Y₀ hY₀ q) =
      ∫ r : ℝ, dist (actualPhysicalHeightAmplitude00_35V3 u p.1 p.2 r)
        (actualPhysicalHeightAmplitude00_35V3 u q.1 q.2 r) ∂(volume : Measure ℝ) := by
  rw [L1.dist_eq_integral_dist]
  apply integral_congr_ae
  filter_upwards [actualPhysicalHeightAmplitude00Lp1_35V2_coe_ae u Y₀ hY₀ p,
    actualPhysicalHeightAmplitude00Lp1_35V2_coe_ae u Y₀ hY₀ q] with r hp hq
  rw [hp, hq]

/-- The actual L¹-class distance in the 11 channel is exactly the full-line
integral distance of the source amplitudes. -/
theorem actualPhysicalHeightAmplitude11Lp1_35V2_dist_eq_integral
    (u : PhysicalL2) (Y₀ : ℝ) (hY₀ : 0 ≤ Y₀)
    (p q : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) Y₀) :
    dist (actualPhysicalHeightAmplitude11Lp1_35V2 u Y₀ hY₀ p)
      (actualPhysicalHeightAmplitude11Lp1_35V2 u Y₀ hY₀ q) =
      ∫ r : ℝ, dist (actualPhysicalHeightAmplitude11_35V3 u p.1 p.2 r)
        (actualPhysicalHeightAmplitude11_35V3 u q.1 q.2 r) ∂(volume : Measure ℝ) := by
  rw [L1.dist_eq_integral_dist]
  apply integral_congr_ae
  filter_upwards [actualPhysicalHeightAmplitude11Lp1_35V2_coe_ae u Y₀ hY₀ p,
    actualPhysicalHeightAmplitude11Lp1_35V2_coe_ae u Y₀ hY₀ q] with r hp hq
  rw [hp, hq]

end NlsGge.SpectralFoundations
end
