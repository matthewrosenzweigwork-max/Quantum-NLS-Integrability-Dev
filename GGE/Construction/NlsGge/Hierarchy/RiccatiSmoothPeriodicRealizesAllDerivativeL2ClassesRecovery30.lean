import NlsGge.Hierarchy.RiccatiSmoothPeriodicSobolevCarrierFromFourierDecayRecovery30Third
import NlsGge.Hierarchy.RiccatiSmoothClassicalDerivativePhysicalL2AgreementRecovery30Fifth
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

/-- Every smooth period-one input is realized by one actual Sobolev carrier
whose Fourier coefficients are exact, and all of its classical derivatives
through the carrier order agree with the corresponding Fourier-multiplier
L² classes. The witness is chosen once, before the derivative order; neither
coefficient matching nor derivative-class agreement is an extra hypothesis. -/
theorem riccatiSmoothPeriodicRealizesAllDerivativeL2ClassesRecovery30
    (m : ℕ) (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u)
    (hper : Function.Periodic u 1) :
    ∃ x : SobolevHilbert (m : ℝ),
      (∀ n : ℤ,
        (show WeightedHilbert (sobolevModeWeight (m : ℝ)) from x) n =
          physicalFourier
            (ContinuousMap.toLp 2 spatialMeasure ℂ
              (riccatiSmoothPeriodicLiftContinuousMapRecovery30First
                u hu.continuous hper)) n) ∧
      ∀ k : ℕ, ∀ hkm : k ≤ m,
        riccatiSobolevIteratedDerivativeL2CLMRecovery30First m k hkm x =
          ContinuousMap.toLp 2 spatialMeasure ℂ
            (riccatiSmoothPeriodicLiftContinuousMapRecovery30First
              (iteratedDeriv k u)
              (by
                rw [iteratedDeriv_eq_iterate]
                exact (ContDiff.iterate_deriv k hu).continuous)
              (NlsGge.HierarchyRiccati.periodic_iteratedDeriv_of_contDiff
                u hu hper k)) := by
  obtain ⟨x, hcoeff⟩ :=
    riccatiSmoothPeriodic_hasSobolevCarrierWithExactFourierCoefficientsRecovery30
      m u hu hper
  refine ⟨x, hcoeff, ?_⟩
  intro k hkm
  exact riccatiSobolevIteratedDerivativeL2_agrees_classicalRecovery30First
    m k hkm x u hu hper hcoeff

end NlsGge.HierarchyRiccati.Core

end
