import Mathlib
import NlsGge.Atomic.I.I022Core
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

theorem i022 (lower upper : ℝ) (c : BoundedCoefficients lower upper)
    (z : ℤ → ℂ) (hz : z ∈ goodGaussianSet c.val) :
    (∀ m : ℕ, SobolevSquareSummable (m : ℝ) (physicalFourier (physicalOfSequence z))) ∧
    ∀ Λ : ℕ → Finset ℤ, IsExhaustion38 Λ →
      (∀ N m : ℕ, SobolevSquareSummable (m : ℝ)
        (physicalFourier (physicalOfSequence (projFin38 (Λ N) z)))) ∧
      (∀ m : ℕ, Tendsto
        (fun N : ℕ => physFS38 m (physicalOfSequence (projFin38 (Λ N) z))) atTop
        (𝓝 (physFS38 m (physicalOfSequence z)))) ∧
      ∃ B : ℝ, 0 ≤ B ∧ ‖physFS38 1 (physicalOfSequence z)‖ ≤ B ∧
        ∀ N : ℕ, ‖physFS38 1 (physicalOfSequence (projFin38 (Λ N) z))‖ ≤ B :=
  NlsGge.ThirdConsultation.I022C.i022_of PDE.actualBirkhoffTop38 actual_inverse_eq_physicalOfSequence lower upper c z hz

end NlsGge.ThirdConsultation.I
