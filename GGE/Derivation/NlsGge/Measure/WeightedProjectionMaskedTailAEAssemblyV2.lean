import NlsGge.Measure.WeightedProjectionMaskedTailDeterministicPrerequisites

set_option autoImplicit false
set_option pp.maxSteps 10000000
noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators

namespace NlsGge.Measure.WeightedProjectionMaskedTailAEAssemblyV2

/-- Reassemble the AE residual-energy identity from the separately audited
realified-coordinate, masked-summability, norm-series and ENNReal conversion
prerequisites. -/
lemma ae_weightedProjectionTailResidual_sqNorm
    {lower upper : ℝ} (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (s : ℝ) (hs : (1 : ℝ) / 2 < s) (S : Finset ℤ) :
    NlsGge.Measure.WeightedProjectionMaskedTailContracts.ae_weightedProjectionTailResidual_sqNorm
      c s hs S := by
  have hcoords := ae_fullWeightedSequenceRealization_apply c s hs
  filter_upwards [hcoords] with z hzCoord
  let x := fullWeightedSequenceRealization c s z
  let wS := NlsGge.Measure.WeightedProjectionMaskedTailContracts.maskedFullModeWeight c s S
  have hsumX := NlsGge.Measure.WeightedProjectionMaskedTailDeterministicPrerequisites.summable_maskedHilbertCoordinates
    c s S x
  have hsumZ : Summable (fun n : ℤ => wS n * ‖z n‖ ^ 2) := by
    refine hsumX.congr fun n => ?_
    rw [hzCoord n]
  have hwS (n : ℤ) : 0 ≤ wS n := by
    by_cases hn : n ∈ S
    · simp [wS, NlsGge.Measure.WeightedProjectionMaskedTailContracts.maskedFullModeWeight, hn]
    · simpa [wS, NlsGge.Measure.WeightedProjectionMaskedTailContracts.maskedFullModeWeight, hn] using
        (NlsGge.Pilot.fullModeWeight_pos c s n).le
  calc
    ‖NlsGge.Measure.WeightedProjectionMaskedTailContracts.weightedProjectionTailResidual
        c s S (fullWeightedSequenceRealization c s z)‖ ^ 2 =
      ∑' n : ℤ, wS n * ‖z n‖ ^ 2 := by
        rw [NlsGge.Measure.WeightedProjectionMaskedTailDeterministicPrerequisites.tailResidual_norm_sq_tsum]
        apply tsum_congr
        intro n
        rw [hzCoord n]
    _ = (sequenceEnergy wS z).toReal := by
        exact (NlsGge.Measure.WeightedProjectionMaskedTailDeterministicPrerequisites.sequenceEnergy_toReal_eq_tsum
          wS z hwS hsumZ).symm

#check @ae_weightedProjectionTailResidual_sqNorm

end NlsGge.Measure.WeightedProjectionMaskedTailAEAssemblyV2
