import NlsGge.Hierarchy.RiccatiPhysicalH1WeightedDerivativeSquareAfterRawHolderInnerPrerequisitesSecond
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace NlsGge.Pilot

open MeasureTheory
open scoped ComplexConjugate ENNReal

local instance : IsProbabilityMeasure spatialMeasure := by
  unfold spatialMeasure
  infer_instance

/-- The actual L²-by-L² Holder product into L¹ on the physical circle. -/
def physicalL2ProductL1CLM :
    PhysicalL2 →L[ℂ] PhysicalL2 →L[ℂ] Lp ℂ 1 spatialMeasure :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL spatialMeasure 2 2 1

/-- The weak-derivative field multiplied by the conjugate of the canonical
continuous representative, retained as an actual L² vector. -/
def physicalH1StarWeightedDerivativeAfterCanonicalMultiplication
    (x : SobolevHilbert 1) : PhysicalL2 :=
  physicalContinuousFieldMultiplierCLMAfterHolderInnerPrerequisites
    (star (physicalH1CanonicalContinuousRepresentativeCLM x))
    (physicalH1DerivativeL2CLM x)

/-- The real cross-pairing contribution `2 Re ∫ (star U · D)^2`. -/
def physicalH1Q4CrossPairingAfterCanonicalMultiplication
    (x : SobolevHilbert 1) : ℝ :=
  2 * Complex.re (MeasureTheory.L1.integral
    (physicalL2ProductL1CLM
      (physicalH1StarWeightedDerivativeAfterCanonicalMultiplication x)
      (physicalH1StarWeightedDerivativeAfterCanonicalMultiplication x)))

theorem continuous_physicalH1Q4CrossPairingAfterCanonicalMultiplication :
    Continuous physicalH1Q4CrossPairingAfterCanonicalMultiplication := by
  have hstar : Continuous (fun x : SobolevHilbert 1 =>
      star (physicalH1CanonicalContinuousRepresentativeCLM x)) := by
    exact continuous_star.comp physicalH1CanonicalContinuousRepresentativeCLM.continuous
  have hoperator : Continuous (fun x : SobolevHilbert 1 =>
      physicalContinuousFieldMultiplierCLMAfterHolderInnerPrerequisites
        (star (physicalH1CanonicalContinuousRepresentativeCLM x))) :=
    (physicalContinuousFieldMultiplierCLMAfterHolderInnerPrerequisites.continuous.comp hstar)
  have hweighted : Continuous physicalH1StarWeightedDerivativeAfterCanonicalMultiplication := by
    exact hoperator.clm_apply physicalH1DerivativeL2CLM.continuous
  have hproduct : Continuous (fun x : SobolevHilbert 1 =>
      physicalL2ProductL1CLM
        (physicalH1StarWeightedDerivativeAfterCanonicalMultiplication x)
        (physicalH1StarWeightedDerivativeAfterCanonicalMultiplication x)) :=
    (physicalL2ProductL1CLM.continuous.comp hweighted).clm_apply hweighted
  have hfun : physicalH1Q4CrossPairingAfterCanonicalMultiplication =
      fun x => 2 * Complex.re (MeasureTheory.L1.integralCLM
        (α := PhysicalCircle) (E := ℂ) (μ := spatialMeasure)
        (physicalL2ProductL1CLM
          (physicalH1StarWeightedDerivativeAfterCanonicalMultiplication x)
          (physicalH1StarWeightedDerivativeAfterCanonicalMultiplication x))) := by
    funext x
    unfold physicalH1Q4CrossPairingAfterCanonicalMultiplication
    exact congrArg (fun z : ℂ => 2 * Complex.re z) (MeasureTheory.L1.integral_eq _)
  rw [hfun]
  exact continuous_const.mul <| Complex.reCLM.continuous.comp
    ((MeasureTheory.L1.integralCLM
      (α := PhysicalCircle) (E := ℂ) (μ := spatialMeasure)).continuous.comp hproduct)

theorem physicalH1Q4CrossPairingAfterCanonicalMultiplication_eq_integral
    (x : SobolevHilbert 1) :
    physicalH1Q4CrossPairingAfterCanonicalMultiplication x =
      2 * Complex.re (∫ y : PhysicalCircle,
        (star (physicalH1CanonicalContinuousRepresentativeCLM x y) *
          physicalH1DerivativeL2CLM x y) ^ 2 ∂spatialMeasure) := by
  let f : C(PhysicalCircle, ℂ) :=
    physicalH1CanonicalContinuousRepresentativeCLM x
  let d : PhysicalL2 := physicalH1DerivativeL2CLM x
  let v : PhysicalL2 := physicalH1StarWeightedDerivativeAfterCanonicalMultiplication x
  have hv : (v : PhysicalCircle → ℂ) =ᵐ[spatialMeasure]
      fun y => star (f y) * d y := by
    change (((ContinuousLinearMap.mul ℂ ℂ).holder 2
      (ContinuousMap.toLp ∞ spatialMeasure ℂ (star f)) d : PhysicalL2) :
        PhysicalCircle → ℂ) =ᵐ[spatialMeasure] fun y => star (f y) * d y
    exact physicalContinuousHolderField_coe_ae (star f) d
  have hprod := (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder
    (r := (1 : ℝ≥0∞)) v v
  calc
    _ = 2 * Complex.re (∫ y : PhysicalCircle,
        ((physicalL2ProductL1CLM v v : Lp ℂ 1 spatialMeasure) :
          PhysicalCircle → ℂ) y ∂spatialMeasure) := by
      unfold physicalH1Q4CrossPairingAfterCanonicalMultiplication
      rw [MeasureTheory.L1.integral_eq_integral]
    _ = 2 * Complex.re (∫ y : PhysicalCircle,
        (star (f y) * d y) ^ 2 ∂spatialMeasure) := by
      congr 2
      apply integral_congr_ae
      filter_upwards [hprod, hv] with y hprod hv
      change ((physicalL2ProductL1CLM v v : Lp ℂ 1 spatialMeasure) :
        PhysicalCircle → ℂ) y = v y * v y at hprod
      change (v : PhysicalCircle → ℂ) y = star (f y) * d y at hv
      rw [hprod, hv]
      ring

end NlsGge.Pilot

end
