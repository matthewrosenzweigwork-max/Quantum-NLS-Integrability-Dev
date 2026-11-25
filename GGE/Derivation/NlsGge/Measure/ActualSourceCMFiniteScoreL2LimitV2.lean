import NlsGge.Measure.ActualSourceCMFiniteScoreL2CauchyAfterShellIdentityV2
import Mathlib.MeasureTheory.Function.LpSpace.Complete

set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology

namespace NlsGge.Measure

/-- The actual CM finite-score sequence has an L² limit on the unchanged raw
countable Gaussian probability space. The returned representative is
AE-strongly-measurable by the standard Lp API. -/
theorem exists_actualSourceCMFiniteScoreL2Limit_v2
    {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (x : NlsGge.Pilot.WeightedRealHilbert (NlsGge.Pilot.cmModeWeight c)) :
    ∃ S : MeasureTheory.Lp ℝ 2
        (NlsGge.Measure.fullWeightSequenceGaussian c.val),
      Tendsto (fun N : ℕ =>
        NlsGge.Measure.actualSourceCMFiniteScorePartialLp c x N)
        atTop (nhds S) ∧
      MeasureTheory.AEStronglyMeasurable S
        (NlsGge.Measure.fullWeightSequenceGaussian c.val) := by
  obtain ⟨S, hS⟩ := cauchySeq_tendsto_of_complete
    (NlsGge.Measure.actualSourceCMFiniteScoreL2Cauchy_afterShellIdentity_v1 c x)
  exact ⟨S, hS, MeasureTheory.Lp.aestronglyMeasurable S⟩

end NlsGge.Measure
