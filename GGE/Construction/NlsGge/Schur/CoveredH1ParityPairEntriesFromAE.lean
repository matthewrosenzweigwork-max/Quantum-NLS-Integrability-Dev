import NlsGge.Schur.CoveredH1ParityPairOperatorFromAE
import NlsGge.Schur.CoveredH1SpectralFourierEntriesFromIntegrand

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace NlsGge.Schur
open NlsGge.Pilot

/-- The `true`/upper output against the `false`/lower input is the exact
unreflected source coefficient of the first potential. -/
theorem coveredH1ParityPairPotential_upper_entry
    (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (n : ℤ) (m l : Sector n) :
    inner ℂ (parityPairVector n (true, m))
      (coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n
        (parityPairVector n (false, l))) =
      physicalFourier u₁ ((m.val + l.val) / 2) := by
  have heven : (m.val + l.val) % 2 = 0 := by omega
  have hform : inner ℂ (parityPairVector n (true, m))
      (coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n
        (parityPairVector n (false, l))) =
      inner ℂ (spectralBasis m.val)
        (coveredH1SpectralMultiplier u₁ hu₁ (spectralBasis (-l.val))) := by
    simp [parityPairVector, mixedIndex, scalarParityVector,
      coveredH1ParityPairPotential_apply_true,
      coveredH1ScalarParityMultiplier_coe_apply, PiLp.single_apply,
      PiLp.inner_apply, Fintype.sum_bool, Submodule.coe_inner]
  rw [hform, coveredH1SpectralMultiplier_upper_entry]
  simp [heven]

/-- The `false`/lower output against the `true`/upper input is the exact
reflected source coefficient of the independent second potential. -/
theorem coveredH1ParityPairPotential_lower_entry
    (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (n : ℤ) (m l : Sector n) :
    inner ℂ (parityPairVector n (false, m))
      (coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n
        (parityPairVector n (true, l))) =
      physicalFourier u₂ (-(m.val + l.val) / 2) := by
  have heven : (m.val + l.val) % 2 = 0 := by omega
  have hform : inner ℂ (parityPairVector n (false, m))
      (coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n
        (parityPairVector n (true, l))) =
      inner ℂ (spectralBasis (-m.val))
        (coveredH1SpectralMultiplier u₂ hu₂ (spectralBasis l.val)) := by
    simp [parityPairVector, mixedIndex, scalarParityVector,
      coveredH1ParityPairPotential_apply_false,
      coveredH1ScalarParityMultiplier_coe_apply, PiLp.single_apply,
      PiLp.inner_apply, Fintype.sum_bool, Submodule.coe_inner]
  rw [hform, coveredH1SpectralMultiplier_lower_entry]
  simp [heven]

end NlsGge.Schur
