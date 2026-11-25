import NlsGge.Hierarchy.RiccatiPhysicalH1ProjectionPlaneRealizationAfterTendstoPrerequisite
import NlsGge.Hierarchy.RiccatiPhysicalH1CanonicalAndDerivativeCLMAfterDerivativeClassLinearityPrerequisite
import NlsGge.Analysis.H1Fourier
import NlsGge.Sobolev.FiniteFourier
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace NlsGge.Pilot

open NlsGge.Analysis
open MeasureTheory

local instance : IsProbabilityMeasure spatialMeasure := by
  unfold spatialMeasure
  infer_instance

theorem physicalH1FiniteProjection_derivative_isPlane (N : ℕ)
    (x : SobolevHilbert 1) :
    physicalH1DerivativeL2CLM (physicalH1FiniteProjection N x) =
      planeL2 N (derivativePlane N (physicalH1FiniteProjectionPlane N x)) := by
  apply physicalFourierL2.injective
  apply lp.ext
  funext n
  rw [physicalFourierL2_apply, physicalH1DerivativeL2CLM_apply,
    physicalH1FourierDerivativeClass_fourier,
    physicalH1FiniteProjection_fourier,
    physicalFourierL2_apply, physicalFourier_planeL2]
  by_cases hn : n ∈ symmetricModes N
  · have hn' : -(N : ℤ) ≤ n ∧ n ≤ (N : ℤ) := by
      simpa only [symmetricModes, Finset.mem_Icc] using hn
    obtain ⟨i, hi⟩ := modeIndex_covers N n hn'.1 hn'.2
    rw [if_pos hn, ← hi, physicalFourier_planeField]
    simp only [physicalH1FiniteProjectionPlane, derivativePlane]
    simp [fourierMultiplier]
    ring
  · have hout : n < -(N : ℤ) ∨ (N : ℤ) < n := by
      simp only [symmetricModes, Finset.mem_Icc] at hn
      omega
    rw [if_neg hn, physicalFourier_planeField_outside N
      (derivativePlane N (physicalH1FiniteProjectionPlane N x)) n hout]
    simp

theorem physicalH1CanonicalContinuousRepresentative_finiteProjection_eq_plane
    (N : ℕ) (x : SobolevHilbert 1) :
    physicalH1CanonicalContinuousRepresentativeCLM (physicalH1FiniteProjection N x) =
      planeContinuous N (physicalH1FiniteProjectionPlane N x) := by
  have hleft :
      (ContinuousMap.toLp 2 spatialMeasure ℂ)
        (physicalH1CanonicalContinuousRepresentativeCLM (physicalH1FiniteProjection N x)) =
      physicalH1CarrierToL2AfterAcceptedCoordinate (physicalH1FiniteProjection N x) := by
    rw [physicalH1CanonicalContinuousRepresentativeCLM_apply]
    exact physicalH1Continuous_toLp
      (physicalH1CarrierToL2AfterAcceptedCoordinate (physicalH1FiniteProjection N x))
      (physicalH1CarrierToL2AfterAcceptedCoordinate_sobolevSquareSummable
        (physicalH1FiniteProjection N x))
  have hright :
      (ContinuousMap.toLp 2 spatialMeasure ℂ)
        (planeContinuous N (physicalH1FiniteProjectionPlane N x)) =
      planeL2 N (physicalH1FiniteProjectionPlane N x) := rfl
  have hLp := hleft.trans (by
    rw [physicalH1FiniteProjection_realizesPlane])
  haveI : spatialMeasure.IsOpenPosMeasure := by
    unfold spatialMeasure
    infer_instance
  exact (ContinuousMap.toLp_injective (p := 2) (μ := spatialMeasure) (𝕜 := ℂ)) hLp

end NlsGge.Pilot
