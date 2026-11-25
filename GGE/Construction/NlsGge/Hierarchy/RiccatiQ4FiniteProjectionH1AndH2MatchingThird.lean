import NlsGge.Hierarchy.RiccatiPhysicalH1Q4SixthPowerIntegralIdentity
import NlsGge.Hierarchy.RiccatiPhysicalH1FiniteProjectionRepresentatives
import NlsGge.Hierarchy.RiccatiFinitePlaneL2NormIntegral
import NlsGge.Sobolev.PeriodicBridge
import NlsGge.Hierarchy.RiccatiUnitPeriodIntervalToPhysicalHaar
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace NlsGge.HierarchyRiccati

open NlsGge.Pilot
open MeasureTheory
open scoped ComplexConjugate Interval

/-- On an actual finite Fourier projection, the three H¹ lower-order
components are the corresponding period-one plane integrals. -/
theorem finiteProjectionQ4LowerOrderRemainder_eq_plane_integrals
    (N : ℕ) (x : SobolevHilbert 1) :
    physicalH1Q4LowerOrderRemainderAfterCanonicalComponents
        (physicalH1FiniteProjection N x) =
      2 * Complex.re (∫ t in (0 : ℝ)..1,
        (star (planeReal N (physicalH1FiniteProjectionPlane N x) t) *
          planeReal N (derivativePlane N (physicalH1FiniteProjectionPlane N x)) t) ^ 2) +
      8 * (∫ t in (0 : ℝ)..1,
        ‖planeReal N (physicalH1FiniteProjectionPlane N x) t‖ ^ 2 *
          ‖planeReal N (derivativePlane N (physicalH1FiniteProjectionPlane N x)) t‖ ^ 2) +
      2 * (∫ t in (0 : ℝ)..1,
        ‖planeReal N (physicalH1FiniteProjectionPlane N x) t‖ ^ 6) := by
  let z : FourierPlane N := physicalH1FiniteProjectionPlane N x
  have hrep :
      physicalH1CanonicalContinuousRepresentativeCLM (physicalH1FiniteProjection N x) =
        planeContinuous N z := by
    exact physicalH1CanonicalContinuousRepresentative_finiteProjection_eq_plane N x
  have hrepPoint (y : PhysicalCircle) :
      physicalH1CanonicalContinuousRepresentativeCLM
          (physicalH1FiniteProjection N x) y = planeField N z y := by
    have h := congrArg (fun f : C(PhysicalCircle, ℂ) => f y) hrep
    change physicalH1CanonicalContinuousRepresentativeCLM
      (physicalH1FiniteProjection N x) y = planeField N z y at h
    exact h
  have hderiv :
      physicalH1DerivativeL2CLM (physicalH1FiniteProjection N x) =
        planeL2 N (derivativePlane N z) := by
    exact physicalH1FiniteProjection_derivative_isPlane N x
  have hderivAE :
      (physicalH1DerivativeL2CLM (physicalH1FiniteProjection N x) :
        PhysicalCircle → ℂ) =ᵐ[spatialMeasure]
        planeField N (derivativePlane N z) := by
    rw [hderiv]
    exact planeL2_ae N (derivativePlane N z)
  have hcross :
      ∫ y : PhysicalCircle,
        (star (physicalH1CanonicalContinuousRepresentativeCLM
            (physicalH1FiniteProjection N x) y) *
          physicalH1DerivativeL2CLM (physicalH1FiniteProjection N x) y) ^ 2
          ∂spatialMeasure =
      ∫ y : PhysicalCircle,
        (star (planeField N z y) * planeField N (derivativePlane N z) y) ^ 2
          ∂spatialMeasure := by
    apply integral_congr_ae
    filter_upwards [hderivAE] with y hy
    rw [hrepPoint y, hy]
  have hweighted :
      ∫ y : PhysicalCircle,
        ‖physicalH1CanonicalContinuousRepresentativeCLM
            (physicalH1FiniteProjection N x) y‖ ^ 2 *
          ‖physicalH1DerivativeL2CLM (physicalH1FiniteProjection N x) y‖ ^ 2
          ∂spatialMeasure =
      ∫ y : PhysicalCircle,
        ‖planeField N z y‖ ^ 2 * ‖planeField N (derivativePlane N z) y‖ ^ 2
          ∂spatialMeasure := by
    apply integral_congr_ae
    filter_upwards [hderivAE] with y hy
    rw [hrepPoint y, hy]
  have hsixth :
      ∫ y : PhysicalCircle,
        ‖physicalH1CanonicalContinuousRepresentativeCLM
            (physicalH1FiniteProjection N x) y‖ ^ 6 ∂spatialMeasure =
      ∫ y : PhysicalCircle, ‖planeField N z y‖ ^ 6 ∂spatialMeasure := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y =>
      congrArg (fun w : ℂ => ‖w‖ ^ 6) (hrepPoint y)
  have hrem :=
    physicalH1Q4LowerOrderRemainderAfterCanonicalComponents_eq_sum_integrals
      (physicalH1FiniteProjection N x)
  rw [hcross, hweighted, hsixth] at hrem
  have hcrossLift :
      (∫ t in (0 : ℝ)..1,
        (star (planeReal N z t) * planeReal N (derivativePlane N z) t) ^ 2) =
      ∫ y : PhysicalCircle,
        (star (planeField N z y) * planeField N (derivativePlane N z) y) ^ 2
          ∂spatialMeasure := by
    convert unitIntervalIntegral_lift_eq_spatialHaar
      (fun y : PhysicalCircle =>
        (star (planeField N z y) * planeField N (derivativePlane N z) y) ^ 2)
      using 1 <;> rfl
  have hweightedLift :
      (∫ t in (0 : ℝ)..1,
        ‖planeReal N z t‖ ^ 2 * ‖planeReal N (derivativePlane N z) t‖ ^ 2) =
      ∫ y : PhysicalCircle,
        ‖planeField N z y‖ ^ 2 * ‖planeField N (derivativePlane N z) y‖ ^ 2
          ∂spatialMeasure := by
    convert unitIntervalIntegral_lift_eq_spatialHaar
      (fun y : PhysicalCircle =>
        ‖planeField N z y‖ ^ 2 * ‖planeField N (derivativePlane N z) y‖ ^ 2)
      using 1 <;> rfl
  have hsixthLift :
      (∫ t in (0 : ℝ)..1, ‖planeReal N z t‖ ^ 6) =
      ∫ y : PhysicalCircle, ‖planeField N z y‖ ^ 6 ∂spatialMeasure := by
    convert unitIntervalIntegral_lift_eq_spatialHaar
      (fun y : PhysicalCircle => ‖planeField N z y‖ ^ 6) using 1 <;> rfl
  calc
    _ = 2 * Complex.re (∫ y : PhysicalCircle,
          (star (planeField N z y) * planeField N (derivativePlane N z) y) ^ 2
            ∂spatialMeasure) +
        8 * (∫ y : PhysicalCircle,
          ‖planeField N z y‖ ^ 2 * ‖planeField N (derivativePlane N z) y‖ ^ 2
            ∂spatialMeasure) +
        2 * (∫ y : PhysicalCircle, ‖planeField N z y‖ ^ 6 ∂spatialMeasure) := hrem
    _ = _ := by rw [← hcrossLift, ← hweightedLift, ← hsixthLift]

/-- The H² leading term of the smooth finite-plane density is realized by
the genuine physical L² norm of its second Fourier derivative. -/
theorem finitePlaneSecondDerivative_intervalIntegral_eq_L2Norm
    (N : ℕ) (z : FourierPlane N) :
    (∫ t in (0 : ℝ)..1,
      ‖iteratedDeriv 2 (planeReal N z) t‖ ^ 2) =
      ‖planeL2 N (derivativePlane N (derivativePlane N z))‖ ^ 2 := by
  have hiter : (derivativePlane N)^[2] z =
      derivativePlane N (derivativePlane N z) := by
    rw [Function.iterate_succ_apply', Function.iterate_one]
  rw [iteratedDeriv_planeReal, hiter]
  have hlift :
      (∫ t in (0 : ℝ)..1,
        ‖planeReal N (derivativePlane N (derivativePlane N z)) t‖ ^ 2) =
      ∫ y : PhysicalCircle,
        ‖planeField N (derivativePlane N (derivativePlane N z)) y‖ ^ 2
          ∂spatialMeasure := by
    convert unitIntervalIntegral_lift_eq_spatialHaar
      (fun y : PhysicalCircle =>
        ‖planeField N (derivativePlane N (derivativePlane N z)) y‖ ^ 2)
      using 1 <;> rfl
  calc
    _ = ∫ y : PhysicalCircle,
          ‖planeField N (derivativePlane N (derivativePlane N z)) y‖ ^ 2
            ∂spatialMeasure := hlift
    _ = ‖planeL2 N (derivativePlane N (derivativePlane N z))‖ ^ 2 :=
      (finitePlane_derivative_norm_sq_eq_spatial_integral N
        (derivativePlane N z)).symm

end NlsGge.HierarchyRiccati

end
