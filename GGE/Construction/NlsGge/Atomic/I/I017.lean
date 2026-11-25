import Mathlib
import NlsGge.Atomic.I.I017Core
import NlsGge.ThirdConsultation.I.ActualInverseBridge

                                                                                                     
                                                                          
                                                                                                          
                                                                                                                      
                                                                                                              
                                                                                                         
                                                                                                        
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology ContDiff
open NlsGge.Pilot NlsGge.Measure NlsGge.Weights
open NlsGge.SpectralFoundations
open NlsGge.Birkhoff NlsGge.Sobolev38 NlsGge.GKDefinitionDesign
open NlsGge.Atomic.I010 (spectralEnergy)
open NlsGge.ThirdConsultation

namespace NlsGge.ThirdConsultation.I

theorem i017 (lower upper : ℝ) (c : BoundedCoefficients lower upper) (Λ : Finset ℤ) :
    let W := weight c.val
    (∀ w : Λ → ℂ,
      Integrable (fun t : ℝ => W (2 * t) * actualGapHeightE02_38 (finiteGapField Λ w) t) ∧
      Summable (fun n : ℤ => |gapRemainderTermE02_38 W (finiteGapField Λ w) n|) ∧
      (∑ n : Λ, fullWeightRate c.val n * ‖w n‖ ^ 2) ≤
        spectralEnergy W (finiteGapField Λ w) ∧
      remainderForWeight W (finiteGapField Λ w) =
        spectralEnergy W (finiteGapField Λ w) -
          (∑ n : Λ, fullWeightRate c.val n * ‖w n‖ ^ 2)) ∧
    Integrable (fun w : Λ → ℂ => Real.exp (-spectralEnergy W (finiteGapField Λ w)))
      (finiteComplexVolume Λ) ∧
    0 < finiteAbsolutePartition W Λ ∧
    finiteAbsolutePartition W Λ ≤ ∏ n : Λ, Real.pi / fullWeightRate c.val n ∧
    0 < finiteRelativeNormalizer W Λ ∧ finiteRelativeNormalizer W Λ ≤ 1 ∧
    finiteRelativeNormalizer W Λ =
      finiteAbsolutePartition W Λ / (∏ n : Λ, Real.pi / fullWeightRate c.val n) ∧
    finiteGapCoordinateLaw W Λ = (finiteComplexVolume Λ).withDensity
      (fun w => ENNReal.ofReal (Real.exp (-spectralEnergy W (finiteGapField Λ w)) /
        finiteAbsolutePartition W Λ)) ∧
    finiteGapCoordinateLaw W Λ = (gammaΛ38 c.val Λ).withDensity
      (fun w => ENNReal.ofReal (Real.exp (-remainderForWeight W (finiteGapField Λ w)) /
        finiteRelativeNormalizer W Λ)) ∧
    IsProbabilityMeasure (finiteGapCoordinateLaw W Λ) ∧ IsProbabilityMeasure (finiteGapLaw W Λ) :=
  NlsGge.ThirdConsultation.I017C.i017_of PDE.actualBirkhoffTop38 actual_inverse_eq_physicalOfSequence lower upper c Λ

end NlsGge.ThirdConsultation.I
