import NlsGge.Measure.CommonSourceLikelihoodL2CauchyAfterRepresentativePrerequisite

set_option autoImplicit false
noncomputable section

open Filter
open scoped Topology

namespace NlsGge.Measure

variable {lower upper : ℝ}

/-- Completeness of the actual common-source `L²` space supplies a limit for
the finite likelihood sequence of every actual source CM vector. This states
existence and convergence in `Lp ℝ 2`; it does not identify a pointwise
representative or a Radon--Nikodym density. -/
theorem exists_actualSourceCMCommonLikelihoodL2Limit
    (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (x : NlsGge.Pilot.WeightedRealHilbert
      (NlsGge.Pilot.cmModeWeight c)) :
    ∃ f : MeasureTheory.Lp ℝ 2
        (NlsGge.Measure.fullWeightSequenceGaussian c.val),
      Tendsto
        (NlsGge.Measure.commonSourceLikelihoodLpSequenceOfMemLp
          lower upper c (NlsGge.Measure.actualSourceCMSequence c x)
          (fun N => NlsGge.Measure.memLp_commonSourceLikelihoodReal c N
            (NlsGge.Measure.actualSourceCMSequence c x)))
        atTop (nhds f) := by
  exact cauchySeq_tendsto_of_complete
    (NlsGge.Measure.actualSourceCMCommonLikelihoodCauchy c x)

end NlsGge.Measure
