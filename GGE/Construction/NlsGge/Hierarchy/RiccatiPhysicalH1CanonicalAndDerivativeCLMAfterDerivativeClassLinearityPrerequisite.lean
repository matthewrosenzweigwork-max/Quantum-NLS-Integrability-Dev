import NlsGge.Hierarchy.RiccatiPhysicalH1CarrierAfterUnweightedCoordinateSecond
import NlsGge.Hierarchy.RiccatiPhysicalFourierL2RealLinearityPrerequisite
import NlsGge.Hierarchy.RiccatiPhysicalH1RepresentativeLinearityPrerequisite
import NlsGge.Hierarchy.RiccatiPhysicalH1DerivativeClassLinearityPrerequisite
import NlsGge.Analysis.H1Fourier
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

/-! The actual H¹ carrier has a bounded linear canonical continuous
representative and a bounded linear L² Fourier-derivative class. The latter
is still identified with the periodic weak derivative only after the separate
finite-test theorem. -/

namespace NlsGge.Pilot

open NlsGge.Analysis

private theorem physicalH1CarrierLinear_fourier_add
    (x y : SobolevHilbert 1) (n : ℤ) :
    physicalFourier (physicalH1CarrierToL2AfterAcceptedCoordinate (x + y)) n =
      physicalFourier (physicalH1CarrierToL2AfterAcceptedCoordinate x) n +
        physicalFourier (physicalH1CarrierToL2AfterAcceptedCoordinate y) n := by
  rw [← physicalFourierL2_apply]
  rw [physicalH1CarrierToL2AfterAcceptedCoordinate.map_add]
  rw [physicalFourierL2_map_add_actual_apply]
  rw [physicalFourierL2_apply, physicalFourierL2_apply]

private theorem physicalH1CarrierLinear_fourier_smul
    (r : ℝ) (x : SobolevHilbert 1) (n : ℤ) :
    physicalFourier (physicalH1CarrierToL2AfterAcceptedCoordinate (r • x)) n =
      (r : ℂ) * physicalFourier (physicalH1CarrierToL2AfterAcceptedCoordinate x) n := by
  rw [← physicalFourierL2_apply]
  rw [physicalH1CarrierToL2AfterAcceptedCoordinate.map_smul]
  rw [physicalFourierL2_map_real_smul_actual_apply]
  rw [physicalFourierL2_apply]

def physicalH1CanonicalContinuousRepresentativeCLM :
    SobolevHilbert 1 →L[ℝ] C(PhysicalCircle, ℂ) := by
  let f : SobolevHilbert 1 →ₗ[ℝ] C(PhysicalCircle, ℂ) := {
    toFun := physicalH1CarrierContinuousAfterAcceptedCoordinate
    map_add' := by
      intro x y
      exact physicalH1CarrierContinuousAfterAcceptedCoordinate_add x y
    map_smul' := by
      intro r x
      exact physicalH1CarrierContinuousAfterAcceptedCoordinate_smul r x
  }
  exact f.mkContinuous ‖reciprocalBracketL2‖ (by
    intro x
    dsimp [f]
    have h := physicalH1CarrierContinuousAfterAcceptedCoordinate_norm_le x
    simpa only [mul_comm] using! h)

theorem physicalH1CanonicalContinuousRepresentativeCLM_apply
    (x : SobolevHilbert 1) :
    physicalH1CanonicalContinuousRepresentativeCLM x =
      physicalH1CarrierContinuousAfterAcceptedCoordinate x := rfl

def physicalH1DerivativeL2CLM :
    SobolevHilbert 1 →L[ℝ] PhysicalL2 := by
  let f : SobolevHilbert 1 →ₗ[ℝ] PhysicalL2 := {
    toFun := fun x => physicalH1FourierDerivativeClass
      (physicalH1CarrierToL2AfterAcceptedCoordinate x)
      (physicalH1CarrierToL2AfterAcceptedCoordinate_sobolevSquareSummable x)
    map_add' := by
      intro x y
      exact physicalH1DerivativeClass_add_actual x y
    map_smul' := by
      intro r x
      exact physicalH1DerivativeClass_smul_actual r x
  }
  exact f.mkContinuous (2 * Real.pi) (by
    intro x
    have h := physicalH1CarrierDerivativeClass_norm_leAfterAcceptedCoordinate x
    change ‖physicalH1FourierDerivativeClass
      (physicalH1CarrierToL2AfterAcceptedCoordinate x)
      (physicalH1CarrierToL2AfterAcceptedCoordinate_sobolevSquareSummable x)‖ ≤
        (2 * Real.pi) * ‖x‖
    exact h)

theorem physicalH1DerivativeL2CLM_apply (x : SobolevHilbert 1) :
    physicalH1DerivativeL2CLM x =
      physicalH1FourierDerivativeClass
        (physicalH1CarrierToL2AfterAcceptedCoordinate x)
        (physicalH1CarrierToL2AfterAcceptedCoordinate_sobolevSquareSummable x) := rfl

end NlsGge.Pilot
