import NlsGge.Hierarchy.RiccatiPhysicalH1HolderAndInnerNormPrerequisitesSecond
import NlsGge.Hierarchy.RiccatiPhysicalH1CanonicalAndDerivativeCLMAfterDerivativeClassLinearityPrerequisite
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

/-- The continuous L² multiplication action associated with an actual
continuous physical field. The `L∞, L² -> L²` Holder map supplies the operator. -/
def physicalContinuousFieldMultiplierCLMAfterHolderInnerPrerequisites :
    C(PhysicalCircle, ℂ) →L[ℂ] (PhysicalL2 →L[ℂ] PhysicalL2) :=
  ((ContinuousLinearMap.mul ℂ ℂ).holderL spatialMeasure ∞ 2 2).comp
    (ContinuousMap.toLp ∞ spatialMeasure ℂ)

/-- The weighted derivative-square contribution, formed from the actual
canonical H¹ representative and actual L² derivative class. -/
def physicalH1WeightedDerivativeSquareAfterHolderInnerPrerequisites
    (x : SobolevHilbert 1) : ℝ :=
  ‖physicalContinuousFieldMultiplierCLMAfterHolderInnerPrerequisites
      (physicalH1CanonicalContinuousRepresentativeCLM x)
      (physicalH1DerivativeL2CLM x)‖ ^ 2

theorem continuous_physicalH1WeightedDerivativeSquareAfterHolderInnerPrerequisites :
    Continuous physicalH1WeightedDerivativeSquareAfterHolderInnerPrerequisites := by
  have hoperator : Continuous (fun x : SobolevHilbert 1 =>
      physicalContinuousFieldMultiplierCLMAfterHolderInnerPrerequisites
        (physicalH1CanonicalContinuousRepresentativeCLM x)) :=
    (physicalContinuousFieldMultiplierCLMAfterHolderInnerPrerequisites.continuous.comp
      physicalH1CanonicalContinuousRepresentativeCLM.continuous)
  have hproduct : Continuous (fun x : SobolevHilbert 1 =>
      physicalContinuousFieldMultiplierCLMAfterHolderInnerPrerequisites
        (physicalH1CanonicalContinuousRepresentativeCLM x)
        (physicalH1DerivativeL2CLM x)) :=
    hoperator.clm_apply physicalH1DerivativeL2CLM.continuous
  unfold physicalH1WeightedDerivativeSquareAfterHolderInnerPrerequisites
  exact (continuous_norm.comp hproduct).pow 2

theorem physicalH1WeightedDerivativeSquareAfterHolderInnerPrerequisites_eq_integral
    (x : SobolevHilbert 1) :
    physicalH1WeightedDerivativeSquareAfterHolderInnerPrerequisites x =
      ∫ y : PhysicalCircle,
        ‖physicalH1CanonicalContinuousRepresentativeCLM x y‖ ^ 2 *
          ‖physicalH1DerivativeL2CLM x y‖ ^ 2 ∂spatialMeasure := by
  let f : C(PhysicalCircle, ℂ) :=
    physicalH1CanonicalContinuousRepresentativeCLM x
  let d : PhysicalL2 := physicalH1DerivativeL2CLM x
  let m : PhysicalL2 := physicalContinuousFieldMultiplierCLMAfterHolderInnerPrerequisites f d
  have hm : (m : PhysicalCircle → ℂ) =ᵐ[spatialMeasure]
      fun y => f y * d y := by
    change (((ContinuousLinearMap.mul ℂ ℂ).holder 2
      (ContinuousMap.toLp ∞ spatialMeasure ℂ f) d : PhysicalL2) :
        PhysicalCircle → ℂ) =ᵐ[spatialMeasure] fun y => f y * d y
    exact physicalContinuousHolderField_coe_ae f d
  have hnorm : ‖m‖ ^ 2 =
      ∫ y : PhysicalCircle, ‖(m : PhysicalCircle → ℂ) y‖ ^ 2 ∂spatialMeasure := by
    calc
      ‖m‖ ^ 2 = Complex.re (inner ℂ m m) := norm_sq_eq_re_inner (𝕜 := ℂ) m
      _ = Complex.re (∫ y : PhysicalCircle,
          inner ℂ ((m : PhysicalCircle → ℂ) y) ((m : PhysicalCircle → ℂ) y)
            ∂spatialMeasure) := by rw [L2.inner_def]
      _ = ∫ y : PhysicalCircle,
          Complex.re (inner ℂ ((m : PhysicalCircle → ℂ) y)
            ((m : PhysicalCircle → ℂ) y)) ∂spatialMeasure := by
        change Complex.reCLM (∫ y : PhysicalCircle,
          inner ℂ ((m : PhysicalCircle → ℂ) y) ((m : PhysicalCircle → ℂ) y)
            ∂spatialMeasure) = _
        rw [← ContinuousLinearMap.integral_comp_comm Complex.reCLM
          (L2.integrable_inner m m)]
        simp only [Complex.reCLM_apply]
      _ = ∫ y : PhysicalCircle, ‖(m : PhysicalCircle → ℂ) y‖ ^ 2
          ∂spatialMeasure := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun y =>
          complex_inner_self_re_eq_norm_sq_actual ((m : PhysicalCircle → ℂ) y)
  unfold physicalH1WeightedDerivativeSquareAfterHolderInnerPrerequisites
  change ‖m‖ ^ 2 = _
  rw [hnorm]
  apply integral_congr_ae
  filter_upwards [hm] with y hy
  rw [hy]
  simp only [Complex.norm_mul]
  ring

end NlsGge.Pilot

end
