import NlsGge.GK38.EigenvalueCompactnessHeight
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # S7: all-L2 action continuity from its actual endpoints

The continuous primitive is formed only after interval integrability.
-/
set_option autoImplicit false
open Filter Topology Set Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

theorem gapHeight_primitive_continuous38 :
    Continuous (fun p : PhysicalL2 × ℝ => ∫ x in (0 : ℝ)..p.2, actualGapHeightE02_38 p.1 x) := by
  have _hi : ∀ u : PhysicalL2, ∀ b : ℝ,
      IntervalIntegrable (actualGapHeightE02_38 u) volume 0 b :=
    fun u b => (continuous_actualGapHeightE02_38 u).intervalIntegrable 0 b
  exact intervalIntegral.continuous_parametric_primitive_of_continuous gapHeight_joint_continuous_L2_38

theorem gapAction_continuous_of_endpoints38 (n : ℤ)
    (hl : Continuous (fun u : PhysicalL2 => actualGapLowerAllE02_38 u n))
    (hu : Continuous (fun u : PhysicalL2 => actualGapUpperAllE02_38 u n)) :
    Continuous (fun u : PhysicalL2 => actualGapActionAllE02_38 u n) := by
  have he (u : PhysicalL2) : actualGapActionAllE02_38 u n =
      (2 / Real.pi) * ((∫ x in (0 : ℝ)..actualGapUpperAllE02_38 u n, actualGapHeightE02_38 u x) -
        ∫ x in (0 : ℝ)..actualGapLowerAllE02_38 u n, actualGapHeightE02_38 u x) := by
    have hi (a b : ℝ) : IntervalIntegrable (actualGapHeightE02_38 u) volume a b :=
      (continuous_actualGapHeightE02_38 u).intervalIntegrable a b
    rw [actualGapActionAllE02_38,
      intervalIntegral.integral_interval_sub_left (hi 0 _) (hi 0 _)]
  simp_rw [he]
  have huP := gapHeight_primitive_continuous38.comp (continuous_id.prodMk hu)
  have hlP := gapHeight_primitive_continuous38.comp (continuous_id.prodMk hl)
  simpa only [Function.comp_def, Pi.sub_apply, id_eq] using! (huP.sub hlP).const_mul (2 / Real.pi)

end
end NlsGge.GK38
