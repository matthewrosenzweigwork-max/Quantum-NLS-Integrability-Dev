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

theorem i034 (lower upper : ℝ) (c : BoundedCoefficients lower upper) :
    let γ := fullWeightSequenceGaussian c.val
    let R := sequenceRemainder (weight c.val)
    let μ := weightedSequenceLaw (weight c.val)
    let Z := limitNormalizer (weight c.val)
    Integrable R μ ∧ (∫ z : ℤ → ℂ, R z ∂μ) ≤ 1 / (Real.exp 1 * Z) ∧
    freeEnergy38 γ R μ = ENNReal.ofReal (-Real.log Z) ∧
    freeEnergy38 γ R μ < ⊤ ∧
    ∀ ρ : Measure (ℤ → ℂ), IsProbabilityMeasure ρ →
      ENNReal.ofReal (-Real.log Z) ≤ freeEnergy38 γ R ρ ∧
      (freeEnergy38 γ R ρ = ENNReal.ofReal (-Real.log Z) ↔ ρ = μ) :=
  NlsGge.ThirdConsultation.I033C.i034_of PDE.actualBirkhoffTop38 actual_inverse_eq_physicalOfSequence lower upper c

end NlsGge.ThirdConsultation.I
