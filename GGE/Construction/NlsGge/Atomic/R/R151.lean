import Mathlib
import NlsGge.Measure.CountableReconstruction
import NlsGge.Sobolev.RealBasis
import Mathlib.MeasureTheory.Measure.RegularityCompacts

                                                                                                                          
set_option autoImplicit false

open MeasureTheory

namespace NlsGge.ThirdConsultation.R

theorem fullWeightedGaussian_isRadon
    (lower upper : ℝ)
    (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (s : ℝ) (hs : (1 : ℝ) / 2 < s) :
    IsProbabilityMeasure
      (NlsGge.Measure.fullWeightedSequenceGaussian c s) ∧
    MeasureTheory.Measure.InnerRegular
      (NlsGge.Measure.fullWeightedSequenceGaussian c s) :=
  ⟨inferInstance, inferInstance⟩

end NlsGge.ThirdConsultation.R
