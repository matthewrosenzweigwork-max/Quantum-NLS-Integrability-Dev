import NlsGge.Measure.ActualSourceCMFiniteScoreEvaluationPrerequisiteV1
import NlsGge.Measure.CommonSourceLikelihoodFiniteAfterScalarPrerequisite
import NlsGge.Measure.CommonSourceLikelihoodL2Definitions

set_option autoImplicit false
noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace NlsGge.Measure

/-- The actual finite CM score is exactly the centered linear part of the
existing finite likelihood exponent, with the source rate normalization. -/
theorem actualSourceCMFiniteScoreExponentIdentity_v1
    {lower upper : ℝ} (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (x : NlsGge.Pilot.WeightedRealHilbert (NlsGge.Pilot.cmModeWeight c))
    (N : ℕ) (z : ℤ → ℂ) :
    commonSourceLikelihoodExponent lower upper c N
        (actualSourceCMSequence c x) z =
      actualSourceCMFiniteScorePartial c x N z -
        commonSourceLikelihoodEnergy lower upper c N
          (actualSourceCMSequence c x) / 2 := by
  rw [commonSourceLikelihoodExponent, commonSourceLikelihoodEnergy,
    actualSourceCMFiniteScorePartial_eq_coordinate_sum_v1]
  rw [Finset.sum_div, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hinner :
      inner ℝ ((show NlsGge.Pilot.WeightedHilbert
        (NlsGge.Pilot.cmModeWeight c) from x) n) (z n) =
      (star (actualSourceCMSequence c x n) * z n).re := by
    simp [Complex.inner, actualSourceCMSequence]
    <;> ring
  rw [hinner]
  simp [NlsGge.Pilot.cmModeWeight, NlsGge.Pilot.sourceRate,
    actualSourceCMSequence, fullWeightRate]
  ring

end NlsGge.Measure
