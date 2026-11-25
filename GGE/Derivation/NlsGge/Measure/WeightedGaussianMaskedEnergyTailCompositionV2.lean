import NlsGge.Measure.WeightedProjectionMaskedTailDefinitions
import NlsGge.Measure.CountableGaussian

set_option autoImplicit false
set_option pp.maxSteps 10000000
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace NlsGge.Measure.WeightedGaussianMaskedEnergyTailCompositionV2

private def tailRestriction (S : Finset ℤ) (z : ℤ → ℂ) : {n : ℤ // n ∉ S} → ℂ :=
  fun i => z i.1

private def tailExtension (S : Finset ℤ) (u : {n : ℤ // n ∉ S} → ℂ) : ℤ → ℂ :=
  fun n => if hn : n ∈ S then 0 else u ⟨n, by simpa using hn⟩

private def maskedTailEnergy
    {lower upper : ℝ} (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (s : ℝ) (S : Finset ℤ) (u : {n : ℤ // n ∉ S} → ℂ) : ℝ≥0∞ :=
  NlsGge.Measure.sequenceEnergy
    (NlsGge.Measure.WeightedProjectionMaskedTailContracts.maskedFullModeWeight c s S)
    (tailExtension S u)

/-- Extending the actual complement restriction by zero on the finite head does
not change the masked quadratic energy. -/
lemma maskedTailEnergy_comp_restriction
    {lower upper : ℝ} (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (s : ℝ) (S : Finset ℤ) :
    (fun z : ℤ → ℂ => maskedTailEnergy c s S (tailRestriction S z)) =
      (fun z => NlsGge.Measure.sequenceEnergy
        (NlsGge.Measure.WeightedProjectionMaskedTailContracts.maskedFullModeWeight c s S) z) := by
  funext z
  unfold maskedTailEnergy tailRestriction
  unfold NlsGge.Measure.sequenceEnergy
  apply tsum_congr
  intro n
  by_cases hn : n ∈ S
  · simp [tailExtension, NlsGge.Measure.WeightedProjectionMaskedTailContracts.maskedFullModeWeight, hn]
  · simp [tailExtension, NlsGge.Measure.WeightedProjectionMaskedTailContracts.maskedFullModeWeight, hn]

#check @maskedTailEnergy_comp_restriction

end NlsGge.Measure.WeightedGaussianMaskedEnergyTailCompositionV2
