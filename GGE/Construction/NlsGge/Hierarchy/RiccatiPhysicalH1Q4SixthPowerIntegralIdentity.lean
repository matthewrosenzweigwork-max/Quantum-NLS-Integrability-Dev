import NlsGge.Hierarchy.RiccatiPhysicalH1Q4LowerOrderRemainderAfterRawWeightedCrossPrerequisitesThird
import NlsGge.Hierarchy.RiccatiComplexStarMulRealNormPrerequisite
import NlsGge.Hierarchy.RiccatiPhysicalH1Q2ScalarAndL1IntegralPrerequisitesAfterCastReplan
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace NlsGge.Pilot

open MeasureTheory
open scoped ComplexConjugate

local instance : IsProbabilityMeasure spatialMeasure := by
  unfold spatialMeasure
  infer_instance

/-- The actual sixth-power H¹ component is its spatial Haar integral. -/
theorem physicalH1SixthPowerIntegralAfterCanonicalRepresentative_eq_integral
    (x : SobolevHilbert 1) :
    physicalH1SixthPowerIntegralAfterCanonicalRepresentative x =
      ∫ y : PhysicalCircle,
        ‖physicalH1CanonicalContinuousRepresentativeCLM x y‖ ^ 6
          ∂spatialMeasure := by
  let f : C(PhysicalCircle, ℂ) :=
    physicalH1CanonicalContinuousRepresentativeCLM x
  let g : C(PhysicalCircle, ℂ) := (star f * f) ^ 3
  have hgint : Integrable (fun y : PhysicalCircle => g y) spatialMeasure := by
    apply g.continuous.integrable_of_hasCompactSupport
    exact isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _)
  have htoLp :
      ((ContinuousMap.toLp 1 spatialMeasure ℂ g : Lp ℂ 1 spatialMeasure) :
          PhysicalCircle → ℂ) =ᵐ[spatialMeasure] g :=
    ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℂ) spatialMeasure g
  have hpoint (y : PhysicalCircle) : Complex.re (g y) = ‖f y‖ ^ 6 := by
    change Complex.re (((starRingEnd ℂ) (f y) * f y) ^ 3) = ‖f y‖ ^ 6
    rw [Complex.conj_mul']
    rw [← Complex.ofReal_pow]
    rw [← Complex.ofReal_pow]
    simp only [Complex.ofReal_re]
    ring
  unfold physicalH1SixthPowerIntegralAfterCanonicalRepresentative
  calc
    _ = Complex.re (MeasureTheory.L1.integral
        ((ContinuousMap.toLp 1 spatialMeasure ℂ) g)) := by rfl
    _ = Complex.re (∫ y : PhysicalCircle,
        ((ContinuousMap.toLp 1 spatialMeasure ℂ g : Lp ℂ 1 spatialMeasure) y)
          ∂spatialMeasure) := by rw [MeasureTheory.L1.integral_eq_integral]
    _ = Complex.re (∫ y : PhysicalCircle, g y ∂spatialMeasure) := by
      congr 1
      exact integral_congr_ae htoLp
    _ = ∫ y : PhysicalCircle, Complex.re (g y) ∂spatialMeasure := by
      change Complex.reCLM (∫ y : PhysicalCircle, g y ∂spatialMeasure) = _
      rw [← ContinuousLinearMap.integral_comp_comm Complex.reCLM hgint]
      simp only [Complex.reCLM_apply]
    _ = ∫ y : PhysicalCircle, ‖f y‖ ^ 6 ∂spatialMeasure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpoint

/-- The lower-order Q₄ candidate is exactly the sum of its three actual
spatial integral components; the H² leading term is kept separate. -/
theorem physicalH1Q4LowerOrderRemainderAfterCanonicalComponents_eq_sum_integrals
    (x : SobolevHilbert 1) :
    physicalH1Q4LowerOrderRemainderAfterCanonicalComponents x =
      2 * Complex.re (∫ y : PhysicalCircle,
        (star (physicalH1CanonicalContinuousRepresentativeCLM x y) *
          physicalH1DerivativeL2CLM x y) ^ 2 ∂spatialMeasure) +
      8 * (∫ y : PhysicalCircle,
        ‖physicalH1CanonicalContinuousRepresentativeCLM x y‖ ^ 2 *
          ‖physicalH1DerivativeL2CLM x y‖ ^ 2 ∂spatialMeasure) +
      2 * (∫ y : PhysicalCircle,
        ‖physicalH1CanonicalContinuousRepresentativeCLM x y‖ ^ 6 ∂spatialMeasure) := by
  unfold physicalH1Q4LowerOrderRemainderAfterCanonicalComponents
  rw [physicalH1Q4CrossPairingAfterCanonicalMultiplication_eq_integral,
    physicalH1WeightedDerivativeSquareAfterHolderInnerPrerequisites_eq_integral,
    physicalH1SixthPowerIntegralAfterCanonicalRepresentative_eq_integral]

end NlsGge.Pilot

end
