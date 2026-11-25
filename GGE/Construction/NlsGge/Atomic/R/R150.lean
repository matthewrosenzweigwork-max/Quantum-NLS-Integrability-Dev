import Mathlib
import NlsGge.Measure.WeightedGaussianActualFullSupportAfterPrerequisitesV9

                                                                                                                          
set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace NlsGge.ThirdConsultation.R

theorem fullWeightedGaussian_ball_pos
    (lower upper : ℝ)
    (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (s : ℝ) (hs : (1 : ℝ) / 2 < s)
    (y : NlsGge.Pilot.FullWeightedHilbert c s)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    0 < NlsGge.Measure.fullWeightedSequenceGaussian c s
      (Metric.ball y epsilon) :=
  NlsGge.Measure.WeightedGaussianActualFullSupportAfterPrerequisitesV9.actualWeightedGaussian_ball_pos
    c s hs y epsilon hepsilon

end NlsGge.ThirdConsultation.R
