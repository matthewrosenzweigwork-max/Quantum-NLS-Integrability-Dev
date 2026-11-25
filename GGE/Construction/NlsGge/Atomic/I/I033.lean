import Mathlib
import NlsGge.Atomic.I.I033Core
import NlsGge.ThirdConsultation.I.ActualInverseBridge

                                                                                                     
                                                                          
                                                                                                      
                                                                                                             
                         
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology
open NlsGge.Pilot NlsGge.Measure NlsGge.Weights
open NlsGge.SpectralFoundations
open NlsGge.Birkhoff NlsGge.Sobolev38 NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation

namespace NlsGge.ThirdConsultation.I

theorem i033 (lower upper : ℝ) (c : BoundedCoefficients lower upper)
    (ρ : Measure (ℤ → ℂ)) [IsProbabilityMeasure ρ]
    (hac : ρ ≪ fullWeightSequenceGaussian c.val)
    (hK : InformationTheory.klDiv ρ (fullWeightSequenceGaussian c.val) ≠ ⊤)
    (hR : Integrable (sequenceRemainder (weight c.val)) ρ) :
    ρ ≪ weightedSequenceLaw (weight c.val) ∧
    InformationTheory.klDiv ρ (weightedSequenceLaw (weight c.val)) ≠ ⊤ ∧
    (InformationTheory.klDiv ρ (weightedSequenceLaw (weight c.val))).toReal =
      (InformationTheory.klDiv ρ (fullWeightSequenceGaussian c.val)).toReal +
        (∫ z : ℤ → ℂ, sequenceRemainder (weight c.val) z ∂ρ) +
        Real.log (limitNormalizer (weight c.val)) :=
  NlsGge.ThirdConsultation.I033C.i033_of PDE.actualBirkhoffTop38 actual_inverse_eq_physicalOfSequence lower upper c ρ hac hK hR

end NlsGge.ThirdConsultation.I
