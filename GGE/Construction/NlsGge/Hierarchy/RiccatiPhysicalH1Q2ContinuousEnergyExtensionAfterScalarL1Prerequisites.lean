import NlsGge.Hierarchy.RiccatiPhysicalH1CanonicalAndDerivativeCLMAfterDerivativeClassLinearityPrerequisite
import NlsGge.Hierarchy.RiccatiPhysicalH1Q2ScalarAndL1IntegralPrerequisitesAfterCastReplan
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

def physicalH1QuarticIntegralAfterScalarL1Prerequisites
    (f : C(PhysicalCircle, ℂ)) : ℝ :=
  Complex.re (MeasureTheory.L1.integral
    ((ContinuousMap.toLp 1 spatialMeasure ℂ) ((star f * f) ^ 2)))

theorem physicalH1QuarticIntegralAfterScalarL1Prerequisites_eq_integral
    (f : C(PhysicalCircle, ℂ)) :
    physicalH1QuarticIntegralAfterScalarL1Prerequisites f =
      ∫ x : PhysicalCircle, ‖f x‖ ^ 4 ∂spatialMeasure := by
  let g : C(PhysicalCircle, ℂ) := (star f * f) ^ 2
  have hgint : Integrable (fun x : PhysicalCircle => g x) spatialMeasure := by
    apply g.continuous.integrable_of_hasCompactSupport
    exact isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _)
  have htoLp :
      ((ContinuousMap.toLp 1 spatialMeasure ℂ) g : PhysicalCircle → ℂ) =ᵐ[spatialMeasure] g :=
    ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℂ) spatialMeasure g
  have hpoint : ∀ x : PhysicalCircle, Complex.re (g x) = ‖f x‖ ^ 4 := by
    intro x
    change Complex.re (((starRingEnd ℂ) (f x) * f x) ^ 2) = ‖f x‖ ^ 4
    exact complex_quartic_real_identity_afterCastReplan (f x)
  unfold physicalH1QuarticIntegralAfterScalarL1Prerequisites
  calc
    _ = Complex.re (MeasureTheory.L1.integral
        ((ContinuousMap.toLp 1 spatialMeasure ℂ) g)) := by rfl
    _ = Complex.re (∫ x : PhysicalCircle,
        ((ContinuousMap.toLp 1 spatialMeasure ℂ) g : PhysicalCircle → ℂ) x
          ∂spatialMeasure) := by rw [MeasureTheory.L1.integral_eq_integral]
    _ = Complex.re (∫ x : PhysicalCircle, g x ∂spatialMeasure) := by
      congr 1
      exact integral_congr_ae htoLp
    _ = ∫ x : PhysicalCircle, Complex.re (g x) ∂spatialMeasure := by
      change Complex.reCLM (∫ x : PhysicalCircle, g x ∂spatialMeasure) = _
      rw [← ContinuousLinearMap.integral_comp_comm Complex.reCLM hgint]
      simp only [Complex.reCLM_apply]
    _ = ∫ x : PhysicalCircle, ‖f x‖ ^ 4 ∂spatialMeasure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpoint

theorem continuous_physicalH1QuarticIntegralAfterScalarL1Prerequisites :
    Continuous physicalH1QuarticIntegralAfterScalarL1Prerequisites := by
  have hpoly : Continuous (fun f : C(PhysicalCircle, ℂ) => (star f * f) ^ 2) := by
    fun_prop
  have hfun :
      physicalH1QuarticIntegralAfterScalarL1Prerequisites =
        fun f => Complex.re (MeasureTheory.L1.integralCLM
          (α := PhysicalCircle) (E := ℂ) (μ := spatialMeasure)
          ((ContinuousMap.toLp 1 spatialMeasure ℂ) ((star f * f) ^ 2))) := by
    funext f
    unfold physicalH1QuarticIntegralAfterScalarL1Prerequisites
    exact congrArg Complex.re
      (congrFun continuousMap_L1_integral_eq_integralCLM_afterCastReplan
        ((star f * f) ^ 2))
  rw [hfun]
  exact Complex.reCLM.continuous.comp
    ((MeasureTheory.L1.integralCLM (α := PhysicalCircle) (E := ℂ)
        (μ := spatialMeasure)).continuous.comp
      ((ContinuousMap.toLp 1 spatialMeasure ℂ).continuous.comp hpoly))

def physicalH1Q2ContinuousEnergyExtensionAfterScalarL1Prerequisites
    (x : SobolevHilbert 1) : ℝ :=
  ‖physicalH1DerivativeL2CLM x‖ ^ 2 +
    physicalH1QuarticIntegralAfterScalarL1Prerequisites
      (physicalH1CanonicalContinuousRepresentativeCLM x)

theorem continuous_physicalH1Q2ContinuousEnergyExtensionAfterScalarL1Prerequisites :
    Continuous physicalH1Q2ContinuousEnergyExtensionAfterScalarL1Prerequisites := by
  unfold physicalH1Q2ContinuousEnergyExtensionAfterScalarL1Prerequisites
  exact (continuous_norm.comp physicalH1DerivativeL2CLM.continuous).pow 2 |>.add
    (continuous_physicalH1QuarticIntegralAfterScalarL1Prerequisites.comp
      physicalH1CanonicalContinuousRepresentativeCLM.continuous)

theorem physicalH1Q2ContinuousEnergyExtensionAfterScalarL1Prerequisites_eq_carrierCandidate
    (x : SobolevHilbert 1) :
    physicalH1Q2ContinuousEnergyExtensionAfterScalarL1Prerequisites x =
      physicalH1CarrierEnergyCandidateAfterAcceptedCoordinate x := by
  rw [physicalH1Q2ContinuousEnergyExtensionAfterScalarL1Prerequisites,
    physicalH1QuarticIntegralAfterScalarL1Prerequisites_eq_integral,
    physicalH1DerivativeL2CLM_apply,
    physicalH1CanonicalContinuousRepresentativeCLM_apply,
    physicalH1CarrierEnergyCandidateAfterAcceptedCoordinate,
    physicalH1EnergyCandidate]
  rfl

end NlsGge.Pilot
