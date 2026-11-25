import Mathlib
import NlsGge.Atomic.I.I023Core
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

theorem i024 (lower upper : ℝ) (c : BoundedCoefficients lower upper) :
    ∀ z ∈ goodGaussianSet c.val,
      Summable (fun n : ℤ =>
        |gapRemainderTermE02_38 (weight c.val) (physicalOfSequence z) n|) ∧
      0 ≤ remainderForWeight (weight c.val) (physicalOfSequence z) ∧
      sequenceRemainder (weight c.val) z = remainderForWeight (weight c.val) (physicalOfSequence z) ∧
      ∀ Λ : ℕ → Finset ℤ, IsExhaustion38 Λ →
        (∀ N : ℕ, 0 ≤ remainderForWeight (weight c.val)
          (physicalOfSequence (projFin38 (Λ N) z))) ∧
        Tendsto (fun N : ℕ => remainderForWeight (weight c.val)
          (physicalOfSequence (projFin38 (Λ N) z))) atTop
          (𝓝 (remainderForWeight (weight c.val) (physicalOfSequence z))) :=
  NlsGge.ThirdConsultation.I023C.i024_of PDE.actualBirkhoffTop38 actual_inverse_eq_physicalOfSequence lower upper c

end NlsGge.ThirdConsultation.I
