import NlsGge.Hierarchy.RiccatiSobolevIteratedDerivativeL2CLMRecovery30First
import NlsGge.Hierarchy.RiccatiUnitPeriodLiftIocFourierCoefficientBridgeMinimumRecovery30
import NlsGge.Hierarchy.RiccatiPeriodicFourierDerivativeCoefficientRecovery29Second
import NlsGge.Hierarchy.RiccatiPeriodicIteratedDerivClosurePrerequisite
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
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

/-- The actual continuous circle representative obtained from a period-one
real-line function. Endpoint matching is derived from its periodicity. -/
noncomputable def riccatiSmoothPeriodicLiftContinuousMapRecovery30First
    (f : ℝ → ℂ) (hf : Continuous f) (hper : Function.Periodic f 1) :
    C(PhysicalCircle, ℂ) :=
  ⟨AddCircle.liftIoc 1 0 f,
    AddCircle.liftIoc_continuous (by simpa using (hper 0).symm)
      hf.continuousOn⟩

/-- Its ordinary physical L² Fourier coefficient is the exact interval
coefficient of the given real-line representative, with period one and no
normalization factor. -/
theorem physicalFourier_liftContinuousMap_eq_fourierCoeffOnRecovery30First
    (f : ℝ → ℂ) (hf : Continuous f) (hper : Function.Periodic f 1) (n : ℤ) :
    physicalFourier
        (ContinuousMap.toLp 2 spatialMeasure ℂ
          (riccatiSmoothPeriodicLiftContinuousMapRecovery30First f hf hper)) n =
      fourierCoeffOn (by norm_num : (0 : ℝ) < 1) f n := by
  change fourierCoeff
      (ContinuousMap.toLp 2 spatialMeasure ℂ
        (riccatiSmoothPeriodicLiftContinuousMapRecovery30First f hf hper)) n = _
  rw [fourierCoeff_congr_ae
    (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) spatialMeasure
      (riccatiSmoothPeriodicLiftContinuousMapRecovery30First f hf hper))]
  simpa only [riccatiSmoothPeriodicLiftContinuousMapRecovery30First, ContinuousMap.coe_mk] using
    fourierCoeff_unitPeriod_liftIoc_eq_fourierCoeffOnMinimumRecovery30 f n

/-- The order-k Fourier-multiplier L² class agrees with the actual classical
iterated derivative for any concrete source Sobolev vector whose coefficients
are the ordinary physical coefficients of the smooth periodic input. The
coefficient-matching premise is the explicit source-carrier realization
boundary; no derivative-class identity is assumed. -/
theorem riccatiSobolevIteratedDerivativeL2_agrees_classicalRecovery30First
    (m k : ℕ) (hkm : k ≤ m) (x : SobolevHilbert (m : ℝ))
    (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u) (hper : Function.Periodic u 1)
    (hsource : ∀ n : ℤ,
      (show WeightedHilbert (sobolevModeWeight (m : ℝ)) from x) n =
        physicalFourier
          (ContinuousMap.toLp 2 spatialMeasure ℂ
            (riccatiSmoothPeriodicLiftContinuousMapRecovery30First u hu.continuous hper)) n) :
    riccatiSobolevIteratedDerivativeL2CLMRecovery30First m k hkm x =
      ContinuousMap.toLp 2 spatialMeasure ℂ
        (riccatiSmoothPeriodicLiftContinuousMapRecovery30First
          (iteratedDeriv k u)
          (by
            rw [iteratedDeriv_eq_iterate]
            exact (ContDiff.iterate_deriv k hu).continuous)
          (NlsGge.HierarchyRiccati.periodic_iteratedDeriv_of_contDiff u hu hper k)) := by
  apply physicalFourierL2.injective
  apply lp.ext
  funext n
  rw [physicalFourierL2_apply, physicalFourierL2_apply,
    riccatiSobolevIteratedDerivativeL2CLMRecovery30First_fourier]
  calc
    fourierMultiplier n ^ k *
        (show WeightedHilbert (sobolevModeWeight (m : ℝ)) from x) n =
      fourierMultiplier n ^ k *
        physicalFourier
          (ContinuousMap.toLp 2 spatialMeasure ℂ
            (riccatiSmoothPeriodicLiftContinuousMapRecovery30First u hu.continuous hper)) n := by
              rw [hsource n]
    _ = fourierCoeffOn (by norm_num : (0 : ℝ) < 1) (iteratedDeriv k u) n := by
          rw [physicalFourier_liftContinuousMap_eq_fourierCoeffOnRecovery30First
            u hu.continuous hper n]
          exact (riccatiFourierCoeffOn_iteratedDeriv_periodOneRecovery29
            u hu hper k n).symm
    _ = physicalFourier
          (ContinuousMap.toLp 2 spatialMeasure ℂ
            (riccatiSmoothPeriodicLiftContinuousMapRecovery30First
              (iteratedDeriv k u)
              (by
                rw [iteratedDeriv_eq_iterate]
                exact (ContDiff.iterate_deriv k hu).continuous)
              (NlsGge.HierarchyRiccati.periodic_iteratedDeriv_of_contDiff u hu hper k))) n :=
            (physicalFourier_liftContinuousMap_eq_fourierCoeffOnRecovery30First
              (iteratedDeriv k u)
              (by
                rw [iteratedDeriv_eq_iterate]
                exact (ContDiff.iterate_deriv k hu).continuous)
              (NlsGge.HierarchyRiccati.periodic_iteratedDeriv_of_contDiff u hu hper k) n).symm

end NlsGge.HierarchyRiccati.Core

end
