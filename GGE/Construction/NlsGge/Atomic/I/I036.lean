import Mathlib
import NlsGge.Atomic.I.I036Core
import NlsGge.ThirdConsultation.I.ActualInverseBridge

                                                                                                            
                                                                                                          
                                                                                                               
                                                                                                           
                                                                                                                  
                                                                                                               
                                                                                                      
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology ContDiff
open NlsGge.Pilot NlsGge.Measure NlsGge.Weights
open NlsGge.SpectralFoundations
open NlsGge.Birkhoff NlsGge.Sobolev38 NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation

namespace NlsGge.ThirdConsultation.I

theorem i036 (lower upper : ℝ) (c : BoundedCoefficients lower upper) :
    ∀ᵐ u ∂physicalLaw (weight c.val),
      (∀ j : ℕ, 0 ≤ chargeFn38 (j + 2) j u) ∧
      Summable (fun n : ℤ => |gapRemainderTermE02_38 (weight c.val) u n|) ∧
      (∀ S : Finset ℤ,
        (∑ n ∈ S, gapIntW38 (weight c.val) u n) =
          (∑ n ∈ S, fullWeightRate c.val n * actualGapActionAllE02_38 u n) +
            (∑ n ∈ S, gapRemainderTermE02_38 (weight c.val) u n)) ∧
      (∑' n : ℤ, ENNReal.ofReal
        (fullWeightRate c.val n * actualGapActionAllE02_38 u n)) = ⊤ ∧
      (∑' n : ℤ, ENNReal.ofReal (gapIntW38 (weight c.val) u n)) = ⊤ ∧
      spectralEnergyENN (weight c.val) u = ⊤ ∧
      (∑' j : ℕ, ENNReal.ofReal (coefficient c.val j * chargeFn38 (j + 2) j u)) = ⊤ ∧
      Tendsto (fun J : ℕ => ∑ j ∈ Finset.range (J + 1),
        coefficient c.val j * chargeFn38 (j + 2) j u) atTop atTop :=
  NlsGge.ThirdConsultation.I036C.i036_of PDE.actualBirkhoffTop38 actual_inverse_eq_physicalOfSequence
    lower upper c

end NlsGge.ThirdConsultation.I
