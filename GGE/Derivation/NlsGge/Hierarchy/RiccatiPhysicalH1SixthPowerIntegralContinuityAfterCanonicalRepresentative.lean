import NlsGge.Hierarchy.RiccatiPhysicalH1Q2ContinuousEnergyExtensionAfterScalarL1Prerequisites
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace NlsGge.Pilot

open MeasureTheory

local instance : IsProbabilityMeasure spatialMeasure := by
  unfold spatialMeasure
  infer_instance

/-- The sixth-power representative contribution to the Q₄ lower-order
remainder, defined directly from the actual canonical H¹ representative. -/
def physicalH1SixthPowerIntegralAfterCanonicalRepresentative
    (x : SobolevHilbert 1) : ℝ :=
  Complex.re (MeasureTheory.L1.integral
    ((ContinuousMap.toLp 1 spatialMeasure ℂ)
      ((star (physicalH1CanonicalContinuousRepresentativeCLM x) *
        physicalH1CanonicalContinuousRepresentativeCLM x) ^ 3)))

theorem continuous_physicalH1SixthPowerIntegralAfterCanonicalRepresentative :
    Continuous physicalH1SixthPowerIntegralAfterCanonicalRepresentative := by
  have hpoly : Continuous (fun f : C(PhysicalCircle, ℂ) => (star f * f) ^ 3) := by
    fun_prop
  have hfun :
      physicalH1SixthPowerIntegralAfterCanonicalRepresentative =
        fun x => Complex.re (MeasureTheory.L1.integralCLM
          (α := PhysicalCircle) (E := ℂ) (μ := spatialMeasure)
          ((ContinuousMap.toLp 1 spatialMeasure ℂ)
            ((star (physicalH1CanonicalContinuousRepresentativeCLM x) *
              physicalH1CanonicalContinuousRepresentativeCLM x) ^ 3))) := by
    funext x
    unfold physicalH1SixthPowerIntegralAfterCanonicalRepresentative
    exact congrArg Complex.re
      (congrFun continuousMap_L1_integral_eq_integralCLM_afterCastReplan
        ((star (physicalH1CanonicalContinuousRepresentativeCLM x) *
          physicalH1CanonicalContinuousRepresentativeCLM x) ^ 3))
  rw [hfun]
  exact Complex.reCLM.continuous.comp
    ((MeasureTheory.L1.integralCLM (α := PhysicalCircle) (E := ℂ)
        (μ := spatialMeasure)).continuous.comp
      ((ContinuousMap.toLp 1 spatialMeasure ℂ).continuous.comp
        (hpoly.comp physicalH1CanonicalContinuousRepresentativeCLM.continuous)))

end NlsGge.Pilot

end
