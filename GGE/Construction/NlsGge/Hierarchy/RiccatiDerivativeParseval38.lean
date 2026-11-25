import NlsGge.Hierarchy.RiccatiSmoothPeriodicJetsAgreePointwiseRecovery31Second
import NlsGge.Hierarchy.RiccatiSmoothClassicalDerivativePhysicalL2AgreementRecovery30Fifth
import NlsGge.Hierarchy.RiccatiUnitPeriodIntervalToPhysicalHaar
import NlsGge.Hierarchy.RiccatiSobolevJetCoefficientL2BoundRecovery28Second
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace NlsGge.HierarchyRiccati.Core

open NlsGge.Pilot
open MeasureTheory
open scoped ContDiff

local instance : IsProbabilityMeasure spatialMeasure := by
  unfold spatialMeasure
  infer_instance

/-- The squared `L²` norm of a continuous function's class is its
probability-Haar square integral. -/
private theorem toLp_norm_sq_eq_integral38
    (f : C(PhysicalCircle, ℂ)) :
    ‖ContinuousMap.toLp 2 spatialMeasure ℂ f‖ ^ 2 =
      ∫ x : PhysicalCircle, ‖f x‖ ^ 2 ∂spatialMeasure := by
  set g := ContinuousMap.toLp 2 spatialMeasure ℂ f with hg
  have h1 : ‖g‖ ^ 2 = RCLike.re (inner ℂ g g) := (inner_self_eq_norm_sq (𝕜 := ℂ) g).symm
  have h2 : inner ℂ g g = ∫ a : PhysicalCircle, inner ℂ (g a) (g a) ∂spatialMeasure :=
    L2.inner_def g g
  have hint : Integrable (fun a : PhysicalCircle => inner ℂ (g a) (g a)) spatialMeasure :=
    L2.integrable_inner g g
  have h3 : RCLike.re (∫ a : PhysicalCircle, inner ℂ (g a) (g a) ∂spatialMeasure) =
      ∫ a : PhysicalCircle, RCLike.re (inner ℂ (g a) (g a)) ∂spatialMeasure :=
    (integral_re hint).symm
  have hae : ∀ᵐ a ∂spatialMeasure, g a = f a :=
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) spatialMeasure f
  rw [h1, h2, h3]
  apply integral_congr_ae
  filter_upwards [hae] with a ha
  rw [ha, inner_self_eq_norm_sq (𝕜 := ℂ)]

theorem smoothDerivative_parseval38 (j : ℕ) (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u)
    (hper : Function.Periodic u 1) :
    Summable (fun n : ℤ => (2 * Real.pi * |(n : ℝ)|) ^ (2 * j) *
      ‖physicalFourier (ContinuousMap.toLp 2 spatialMeasure ℂ
        (riccatiSmoothPeriodicLiftContinuousMapRecovery30First u hu.continuous hper)) n‖ ^ 2) ∧
    (∫ x in (0 : ℝ)..1, ‖iteratedDeriv j u x‖ ^ 2) =
      ∑' n : ℤ, (2 * Real.pi * |(n : ℝ)|) ^ (2 * j) *
        ‖physicalFourier (ContinuousMap.toLp 2 spatialMeasure ℂ
          (riccatiSmoothPeriodicLiftContinuousMapRecovery30First u hu.continuous hper)) n‖ ^ 2 := by
  obtain ⟨x, hsource, -⟩ := riccatiSmoothPeriodicJetsAgreePointwiseRecovery31Second j u hu hper
  have hagree := riccatiSobolevIteratedDerivativeL2_agrees_classicalRecovery30First
    j j le_rfl x u hu hper hsource
  set F := riccatiSmoothPeriodicLiftContinuousMapRecovery30First
    (iteratedDeriv j u)
    (by
      rw [iteratedDeriv_eq_iterate]
      exact (ContDiff.iterate_deriv j hu).continuous)
    (NlsGge.HierarchyRiccati.periodic_iteratedDeriv_of_contDiff u hu hper j) with hF
  set g := riccatiSobolevIteratedDerivativeL2CLMRecovery30First j j le_rfl x with hgdef
  have hterm : ∀ n : ℤ, ‖physicalFourier g n‖ ^ 2 =
      (2 * Real.pi * |(n : ℝ)|) ^ (2 * j) *
        ‖physicalFourier (ContinuousMap.toLp 2 spatialMeasure ℂ
          (riccatiSmoothPeriodicLiftContinuousMapRecovery30First u hu.continuous hper)) n‖ ^ 2 := by
    intro n
    rw [hgdef, riccatiSobolevIteratedDerivativeL2CLMRecovery30First_fourier,
      riccatiSobolevJetCoefficient_norm_sqL2Recovery28Second, ← hsource n]
    ring
  have hsum := hasSum_physicalFourier_sq g
  have hsum' : HasSum (fun n : ℤ => (2 * Real.pi * |(n : ℝ)|) ^ (2 * j) *
      ‖physicalFourier (ContinuousMap.toLp 2 spatialMeasure ℂ
        (riccatiSmoothPeriodicLiftContinuousMapRecovery30First u hu.continuous hper)) n‖ ^ 2)
      (‖g‖ ^ 2) := by
    simpa only [hterm] using hsum
  refine ⟨hsum'.summable, ?_⟩
  rw [hsum'.tsum_eq, hagree, toLp_norm_sq_eq_integral38]
  rw [intervalIntegral.integral_of_le zero_le_one]
  rw [← intervalIntegral.integral_of_le zero_le_one]
  have := unitIntervalIntegral_lift_eq_spatialHaar
    (fun y : PhysicalCircle => ‖F y‖ ^ 2)
  rw [← this]
  rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t ht
  have ht' : t ∈ Set.Ioc (0 : ℝ) (0 + 1) := by simpa using ht
  simp only [hF, riccatiSmoothPeriodicLiftContinuousMapRecovery30First, ContinuousMap.coe_mk,
    AddCircle.liftIoc_coe_apply ht']

end NlsGge.HierarchyRiccati.Core
