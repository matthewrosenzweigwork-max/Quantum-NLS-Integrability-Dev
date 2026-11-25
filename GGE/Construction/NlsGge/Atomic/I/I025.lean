import Mathlib
import NlsGge.Atomic.I.I025Core
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

theorem i025 (lower upper : ℝ) (c : BoundedCoefficients lower upper) :
    let W := weight c.val
    let γ := fullWeightSequenceGaussian c.val
    Measurable physicalOfSequence ∧ Measurable (sequenceRemainder W) ∧
    Integrable (fun z : ℤ → ℂ => Real.exp (-sequenceRemainder W z)) γ ∧
    (∀ᵐ z ∂γ, sequenceRemainder W z = remainder38 c.val (physicalOfSequence z) ∧
      0 < Real.exp (-sequenceRemainder W z) ∧ Real.exp (-sequenceRemainder W z) ≤ 1) ∧
    0 < limitNormalizer W ∧ limitNormalizer W ≤ 1 ∧
    weightedSequenceLaw W = γ.withDensity
      (fun z => ENNReal.ofReal (Real.exp (-sequenceRemainder W z) / limitNormalizer W)) ∧
    IsProbabilityMeasure (weightedSequenceLaw W) ∧ IsProbabilityMeasure (physicalLaw W) ∧
    weightedSequenceLaw W ≪ γ ∧ γ ≪ weightedSequenceLaw W ∧
    (∀ᵐ z ∂weightedSequenceLaw W, z ∈ goodGaussianSet c.val) :=
  NlsGge.ThirdConsultation.I025C.i025_of PDE.actualBirkhoffTop38 actual_inverse_eq_physicalOfSequence lower upper c

end NlsGge.ThirdConsultation.I
