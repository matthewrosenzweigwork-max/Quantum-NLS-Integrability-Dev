import NlsGge.Sobolev.PhysicalProjection

set_option autoImplicit false
set_option pp.maxSteps 10000000

namespace NlsGge.Measure.WeightedGaussianFullWeightedProjectionDistanceBridgeV1

/-- The convergence distance supplied by the complex weighted Hilbert projection
is exactly the real full-weighted norm used by the Gaussian support target. -/
lemma projection_distance_eq_fullWeighted_norm
    {lower upper : ℝ} (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (s : ℝ) (x : NlsGge.Pilot.FullWeightedHilbert c s) (S : Finset ℤ) :
    dist
      (NlsGge.Pilot.weightedProjection (NlsGge.Pilot.fullModeWeight c s) S
        (show NlsGge.Pilot.WeightedHilbert (NlsGge.Pilot.fullModeWeight c s) from x))
      (show NlsGge.Pilot.WeightedHilbert (NlsGge.Pilot.fullModeWeight c s) from x) =
    ‖x - (show NlsGge.Pilot.FullWeightedHilbert c s from
      NlsGge.Pilot.weightedProjection (NlsGge.Pilot.fullModeWeight c s) S
        (show NlsGge.Pilot.WeightedHilbert (NlsGge.Pilot.fullModeWeight c s) from x))‖ := by
  rw [dist_comm, dist_eq_norm]
  rfl

#check @projection_distance_eq_fullWeighted_norm

end NlsGge.Measure.WeightedGaussianFullWeightedProjectionDistanceBridgeV1
