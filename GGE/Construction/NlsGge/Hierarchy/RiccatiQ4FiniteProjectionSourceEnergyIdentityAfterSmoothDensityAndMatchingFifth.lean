import NlsGge.Hierarchy.RiccatiQ4SmoothPeriodicIdentityAfterEvaluationPrerequisitesSecond
import NlsGge.Hierarchy.RiccatiQ4SmoothDensityPointwiseAfterCheckedAlgebraAndStarPrerequisites
import NlsGge.Hierarchy.RiccatiQ4FiniteProjectionH1AndH2MatchingThird
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace NlsGge.HierarchyRiccati

open NlsGge.Pilot
open NlsGge.HierarchyRiccati.Core
open MeasureTheory
open scoped ComplexConjugate ContDiff Interval

/-- For a finite physical H¹ projection, the smooth periodic Q₄ source
integral is the genuine second-derivative L² energy plus the actual H¹
lower-order remainder. The leading H² quantity is kept explicit. -/
theorem finiteProjectionQ4SourceIntegral_eq_secondDerivativeL2_add_H1Remainder
    (N : ℕ) (x : SobolevHilbert 1) :
    Complex.re (∫ t in (0 : ℝ)..1,
      q4SourceDensityAfterEvaluationPrerequisites
        (planeReal N (physicalH1FiniteProjectionPlane N x)) t) =
      ‖planeL2 N (derivativePlane N
        (derivativePlane N (physicalH1FiniteProjectionPlane N x)))‖ ^ 2 +
        physicalH1Q4LowerOrderRemainderAfterCanonicalComponents
          (physicalH1FiniteProjection N x) := by
  let z : FourierPlane N := physicalH1FiniteProjectionPlane N x
  let u : ℝ → ℂ := planeReal N z
  have hu : ContDiff ℝ ∞ u := by
    dsimp [u]
    exact (contDiff_planeReal N z).of_le (by simp)
  have hper : Function.Periodic u 1 := by
    intro t
    dsimp [u]
    exact planeReal_periodic N z t
  have hsource := q4_smooth_periodic_source_integral_identity_after_evaluation_prerequisites
    u hu hper
  have henergyPolyCont : Continuous
      (q4EnergyPolynomialDensityAfterEvaluationPrerequisites u) := by
    rw [continuous_iff_continuousAt]
    intro t
    exact (riccatiJetEvaluation_hasDerivAt u hu
      q4EnergyPolynomialAfterEvaluationPrerequisites t).continuousAt
  have henergyEq : q4EnergyDensityAfterEvaluationPrerequisites u =
      q4EnergyPolynomialDensityAfterEvaluationPrerequisites u := by
    funext t
    exact (q4EnergyPolynomialDensity_eq_explicit_after_evaluation_prerequisites
      u t).symm
  have henergyCont : Continuous (q4EnergyDensityAfterEvaluationPrerequisites u) := by
    rw [henergyEq]
    exact henergyPolyCont
  have henergyInt : IntervalIntegrable
      (q4EnergyDensityAfterEvaluationPrerequisites u) MeasureTheory.volume 0 1 :=
    henergyCont.continuousOn.intervalIntegrable
  have hD1 : ContDiff ℝ ∞ (iteratedDeriv 1 u) := by
    rw [iteratedDeriv_eq_iterate]
    exact ContDiff.iterate_deriv 1 hu
  have hD2 : ContDiff ℝ ∞ (iteratedDeriv 2 u) := by
    rw [iteratedDeriv_eq_iterate]
    exact ContDiff.iterate_deriv 2 hu
  have hUCont : Continuous u := hu.continuous
  have hD1Cont : Continuous (iteratedDeriv 1 u) := hD1.continuous
  have hdu : iteratedDeriv 1 u = fun t => planeReal N (derivativePlane N z) t := by
    dsimp [u]
    rw [iteratedDeriv_planeReal]
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  have hleadingCont : Continuous (fun t => ‖iteratedDeriv 2 u t‖ ^ 2) :=
    (hD2.continuous.norm).pow 2
  have hlowerCont : Continuous
      (q4SmoothLowerOrderRealDensityAfterCheckedPrerequisites u) := by
    have hsplit t := q4EnergyDensity_eq_h2_leading_add_lower_order_after_checked_prerequisites
      u t
    have hEq : q4SmoothLowerOrderRealDensityAfterCheckedPrerequisites u =
        fun t => Complex.re (q4EnergyDensityAfterEvaluationPrerequisites u t) -
          ‖iteratedDeriv 2 u t‖ ^ 2 := by
      funext t
      have ht := hsplit t
      linarith
    rw [hEq]
    exact (Complex.reCLM.continuous.comp henergyCont).sub hleadingCont
  have hleadingInt : IntervalIntegrable
      (fun t => ‖iteratedDeriv 2 u t‖ ^ 2) MeasureTheory.volume 0 1 :=
    hleadingCont.continuousOn.intervalIntegrable
  have hlowerInt : IntervalIntegrable
      (q4SmoothLowerOrderRealDensityAfterCheckedPrerequisites u)
      MeasureTheory.volume 0 1 := hlowerCont.continuousOn.intervalIntegrable
  have hsplitInt :
      (∫ t in (0 : ℝ)..1,
        Complex.re (q4EnergyDensityAfterEvaluationPrerequisites u t)) =
        (∫ t in (0 : ℝ)..1, ‖iteratedDeriv 2 u t‖ ^ 2) +
          ∫ t in (0 : ℝ)..1,
            q4SmoothLowerOrderRealDensityAfterCheckedPrerequisites u t := by
    calc
      _ = ∫ t in (0 : ℝ)..1,
          (‖iteratedDeriv 2 u t‖ ^ 2 +
            q4SmoothLowerOrderRealDensityAfterCheckedPrerequisites u t) := by
        apply intervalIntegral.integral_congr
        intro t ht
        exact q4EnergyDensity_eq_h2_leading_add_lower_order_after_checked_prerequisites
          u t
      _ = _ := intervalIntegral.integral_add hleadingInt hlowerInt
  have hcrossComplexCont : Continuous (fun t =>
      (star (u t) * iteratedDeriv 1 u t) ^ 2) := by
    fun_prop
  have hcrossComplexInt : IntervalIntegrable (fun t =>
      (star (u t) * iteratedDeriv 1 u t) ^ 2)
      MeasureTheory.volume 0 1 := hcrossComplexCont.continuousOn.intervalIntegrable
  have hcrossCont : Continuous (fun t =>
      2 * Complex.re ((star (u t) * iteratedDeriv 1 u t) ^ 2)) := by
    fun_prop
  have hweightCont : Continuous (fun t =>
      8 * ‖u t‖ ^ 2 * ‖iteratedDeriv 1 u t‖ ^ 2) := by
    fun_prop
  have hsixthCont : Continuous (fun t => 2 * ‖u t‖ ^ 6) := by
    fun_prop
  have hcrossInt : IntervalIntegrable (fun t =>
      2 * Complex.re ((star (u t) * iteratedDeriv 1 u t) ^ 2))
      MeasureTheory.volume 0 1 := hcrossCont.continuousOn.intervalIntegrable
  have hweightInt : IntervalIntegrable (fun t =>
      8 * ‖u t‖ ^ 2 * ‖iteratedDeriv 1 u t‖ ^ 2)
      MeasureTheory.volume 0 1 := hweightCont.continuousOn.intervalIntegrable
  have hsixthInt : IntervalIntegrable (fun t => 2 * ‖u t‖ ^ 6)
      MeasureTheory.volume 0 1 := hsixthCont.continuousOn.intervalIntegrable
  have hcrossReal :
      (∫ t in (0 : ℝ)..1,
        2 * Complex.re ((star (u t) * iteratedDeriv 1 u t) ^ 2)) =
        2 * Complex.re (∫ t in (0 : ℝ)..1,
          (star (u t) * iteratedDeriv 1 u t) ^ 2) := by
    calc
      _ = 2 * (∫ t in (0 : ℝ)..1,
          Complex.re ((star (u t) * iteratedDeriv 1 u t) ^ 2)) := by
        rw [intervalIntegral.integral_const_mul]
      _ = _ := by
        exact congrArg (fun r : ℝ => 2 * r)
          (by simpa only [Complex.reCLM_apply] using
            Complex.reCLM.intervalIntegral_comp_comm hcrossComplexInt)
  have hweightAssoc :
      (∫ t in (0 : ℝ)..1,
        8 * ‖u t‖ ^ 2 * ‖iteratedDeriv 1 u t‖ ^ 2) =
        8 * (∫ t in (0 : ℝ)..1,
          ‖u t‖ ^ 2 * ‖iteratedDeriv 1 u t‖ ^ 2) := by
    calc
      _ = ∫ t in (0 : ℝ)..1,
          8 * (‖u t‖ ^ 2 * ‖iteratedDeriv 1 u t‖ ^ 2) := by
        apply intervalIntegral.integral_congr
        intro t ht
        ring
      _ = _ := by rw [intervalIntegral.integral_const_mul]
  have hsixthIntegral :
      (∫ t in (0 : ℝ)..1, 2 * ‖u t‖ ^ 6) =
        2 * (∫ t in (0 : ℝ)..1, ‖u t‖ ^ 6) := by
    rw [intervalIntegral.integral_const_mul]
  have hlowerPlane :
      (∫ t in (0 : ℝ)..1,
        q4SmoothLowerOrderRealDensityAfterCheckedPrerequisites u t) =
      2 * Complex.re (∫ t in (0 : ℝ)..1,
          (star (planeReal N z t) * planeReal N (derivativePlane N z) t) ^ 2) +
        8 * (∫ t in (0 : ℝ)..1,
          ‖planeReal N z t‖ ^ 2 * ‖planeReal N (derivativePlane N z) t‖ ^ 2) +
        2 * (∫ t in (0 : ℝ)..1, ‖planeReal N z t‖ ^ 6) := by
    calc
      _ = ∫ t in (0 : ℝ)..1,
          (2 * Complex.re ((star (u t) * iteratedDeriv 1 u t) ^ 2) +
            (8 * ‖u t‖ ^ 2 * ‖iteratedDeriv 1 u t‖ ^ 2 + 2 * ‖u t‖ ^ 6)) := by
        apply intervalIntegral.integral_congr
        intro t ht
        simp only [q4SmoothLowerOrderRealDensityAfterCheckedPrerequisites]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_add hcrossInt (hweightInt.add hsixthInt)]
        rw [intervalIntegral.integral_add hweightInt hsixthInt]
        rw [hcrossReal, hweightAssoc, hsixthIntegral]
        simp only [u, hdu]
        ring
  have hmatching := finiteProjectionQ4LowerOrderRemainder_eq_plane_integrals N x
  have hlowerRemainder :
      (∫ t in (0 : ℝ)..1,
        q4SmoothLowerOrderRealDensityAfterCheckedPrerequisites u t) =
      physicalH1Q4LowerOrderRemainderAfterCanonicalComponents
        (physicalH1FiniteProjection N x) := by
    rw [hlowerPlane]
    exact hmatching.symm
  calc
    _ = Complex.re (∫ t in (0 : ℝ)..1,
        q4EnergyDensityAfterEvaluationPrerequisites u t) := by
      exact congrArg Complex.re hsource
    _ = ∫ t in (0 : ℝ)..1,
        Complex.re (q4EnergyDensityAfterEvaluationPrerequisites u t) := by
      simpa only [Complex.reCLM_apply] using
        (Complex.reCLM.intervalIntegral_comp_comm henergyInt).symm
    _ = _ := by
      rw [hsplitInt, finitePlaneSecondDerivative_intervalIntegral_eq_L2Norm,
        hlowerRemainder]

end NlsGge.HierarchyRiccati

end
