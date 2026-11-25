import NlsGge.Measure.WeightedModes
import NlsGge.Sobolev.PhysicalProjection

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace NlsGge.Measure

lemma ae_fullWeightedSequencePartial_dual_eq_weightedRealProjection
    {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) (N : ℕ)
    (L : NlsGge.Pilot.FullWeightedHilbert c s →L[ℝ] ℝ) :
    (fun z : ℤ → ℂ =>
      L (NlsGge.Measure.fullWeightedSequencePartial c s N z)) =ᵐ[
      NlsGge.Measure.fullWeightSequenceGaussian c.val]
    (fun z : ℤ → ℂ =>
      L (NlsGge.Pilot.weightedRealProjectionContinuous
        (NlsGge.Pilot.fullModeWeight c s)
        (NlsGge.Pilot.symmetricModes N)
        (NlsGge.Measure.fullWeightedSequenceRealization c s z))) := by
  filter_upwards [ae_fullWeightedSequenceRealization_apply c s hs] with z hz
  have hpartial : fullWeightedSequencePartial c s N z =
      NlsGge.Pilot.weightedRealProjectionContinuous
        (NlsGge.Pilot.fullModeWeight c s)
        (NlsGge.Pilot.symmetricModes N)
        (fullWeightedSequenceRealization c s z) := by
    change fullWeightedSequencePartial c s N z =
      NlsGge.Pilot.weightedProjection (NlsGge.Pilot.fullModeWeight c s)
        (NlsGge.Pilot.symmetricModes N)
        (show NlsGge.Pilot.WeightedHilbert (NlsGge.Pilot.fullModeWeight c s) from
          fullWeightedSequenceRealization c s z)
    unfold fullWeightedSequencePartial NlsGge.Pilot.weightedProjection
    apply congrArg (NlsGge.Pilot.weightedIsometry
      (NlsGge.Pilot.fullModeWeight c s)).symm
    apply Finset.sum_congr rfl
    intro n hn
    apply congrArg (lp.single (E := fun _ : ℤ => ℂ) 2 n)
    change NlsGge.Pilot.weightedCoordinates (NlsGge.Pilot.fullModeWeight c s) z n =
      NlsGge.Pilot.weightedCoordinates (NlsGge.Pilot.fullModeWeight c s)
        (fun j => (show NlsGge.Pilot.WeightedHilbert
          (NlsGge.Pilot.fullModeWeight c s) from
            fullWeightedSequenceRealization c s z) j) n
    unfold NlsGge.Pilot.weightedCoordinates
    exact congrArg (fun value : ℂ =>
      (Real.sqrt (NlsGge.Pilot.fullModeWeight c s n) : ℂ) * value) (hz n).symm
  exact congrArg L hpartial

end NlsGge.Measure
