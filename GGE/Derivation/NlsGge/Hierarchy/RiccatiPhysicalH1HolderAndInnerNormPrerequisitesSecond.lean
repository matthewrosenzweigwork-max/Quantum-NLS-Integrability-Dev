import NlsGge.Analysis.H1Multiplication
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace NlsGge.Pilot

open MeasureTheory
open scoped ENNReal

local instance : IsProbabilityMeasure spatialMeasure := by
  unfold spatialMeasure
  infer_instance

/-- The L² output of the physical Holder multiplication has the expected
continuous-field representative. This isolates the two actual a.e. casts. -/
theorem physicalContinuousHolderField_coe_ae
    (f : C(PhysicalCircle, ℂ)) (d : PhysicalL2) :
    (((ContinuousLinearMap.mul ℂ ℂ).holder 2
      (ContinuousMap.toLp ∞ spatialMeasure ℂ f) d : PhysicalL2) :
        PhysicalCircle → ℂ) =ᵐ[spatialMeasure] fun y => f y * d y := by
  have hmul := (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder
    (r := (2 : ℝ≥0∞)) (ContinuousMap.toLp ∞ spatialMeasure ℂ f) d
  have hf := ContinuousMap.coeFn_toLp (p := ∞) (𝕜 := ℂ) spatialMeasure f
  have hmul' : (((ContinuousLinearMap.mul ℂ ℂ).holder 2
      (ContinuousMap.toLp ∞ spatialMeasure ℂ f) d : PhysicalL2) :
        PhysicalCircle → ℂ) =ᵐ[spatialMeasure]
      fun y => ((ContinuousMap.toLp ∞ spatialMeasure ℂ f :
        PhysicalCircle → ℂ) y) * d y := by
    simpa only [ContinuousLinearMap.mul_apply'] using hmul
  filter_upwards [hmul', hf] with y hy hf
  change (ContinuousMap.toLp ∞ spatialMeasure ℂ f : PhysicalCircle → ℂ) y = f y at hf
  rw [hy, hf]

theorem complex_inner_self_re_eq_norm_sq_actual (z : ℂ) :
    Complex.re (inner ℂ z z) = ‖z‖ ^ 2 := by
  exact inner_self_eq_norm_sq (𝕜 := ℂ) z

end NlsGge.Pilot

end
