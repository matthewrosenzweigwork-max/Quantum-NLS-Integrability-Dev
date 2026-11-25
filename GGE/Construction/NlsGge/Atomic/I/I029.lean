import Mathlib
import NlsGge.ThirdConsultation.I.I029Core
import NlsGge.ThirdConsultation.I.ActualEnsembleBridge
import NlsGge.ThirdConsultation.I.ActualInverseBridge
import NlsGge.ThirdConsultation.PDE.BirkhoffRealization
import NlsGge.Atomic.G6.G6028
import NlsGge.Atomic.G6.G6013

                                                                                                            
                                                                                                                        
                                                                                                                         
                                                                                                                              
                                                                              
                                                                                                                
                                                                                                                           
                                                  set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology ContDiff BoundedContinuousFunction
open NlsGge.Pilot NlsGge.Measure NlsGge.Weights
open NlsGge.SpectralFoundations
open NlsGge.Birkhoff NlsGge.Sobolev38 NlsGge.GKDefinitionDesign
open NlsGge.Atomic.I010 (spectralEnergy)
open NlsGge.ThirdConsultation

namespace NlsGge.ThirdConsultation.I

theorem i029 (lower upper : ℝ) (c : BoundedCoefficients lower upper) :
    (∀ m : ℕ, ∃ A : ℝ, 0 < A ∧ ∃ d : ℕ,
      ∀ z : ℤ → ℂ, SobolevSquareSummable (m : ℝ) z →
        ‖physFS38 m (physicalOfSequence z)‖ ≤ A * (1 + sobolevSeqNorm m z) ^ d) ∧
    (∀ z : ℤ → ℂ, SobolevSquareSummable 0 z →
      ‖physicalOfSequence z‖ = sobolevSeqNorm 0 z) ∧
    (∀ᵐ (u : PhysicalL2) ∂physicalLaw (weight c.val),
      ∀ m : ℕ, SobolevSquareSummable (m : ℝ) (physicalFourier u)) ∧
    ∀ (m : ℕ) (q : ℝ), 0 ≤ q →
      Integrable (fun z : ℤ → ℂ => ‖physFS38 m (physicalOfSequence z)‖ ^ q)
        (fullWeightSequenceGaussian c.val) ∧
      Integrable (fun u : PhysicalL2 => ‖physFS38 m u‖ ^ q) (physicalLaw (weight c.val)) ∧
      (∫ u : PhysicalL2, ‖physFS38 m u‖ ^ q ∂physicalLaw (weight c.val)) ≤
        (limitNormalizer (weight c.val))⁻¹ *
          (∫ z : ℤ → ℂ, ‖physFS38 m (physicalOfSequence z)‖ ^ q
            ∂fullWeightSequenceGaussian c.val) :=
  I029Aux.i029_of lower upper c PDE.actualBirkhoffTop38 PDE.actualBirkhoffMolnar38
    actual_inverse_eq_physicalOfSequence (actual_ensemble_eq_I lower upper c).2.2.1
    (actual_ensemble_eq_I lower upper c).1
    (fun u n => ((G6028).1 u n).2.2) G6028.2.1 G6013.2.2.2.2.2

end NlsGge.ThirdConsultation.I
