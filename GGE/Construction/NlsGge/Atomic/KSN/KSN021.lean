import Mathlib
import NlsGge.Atomic.KSN.KSN021Of
import NlsGge.Atomic.M.M049

                                                                                                      
                                                                                                                   
                                                                                                          
set_option autoImplicit false
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Atomic.Common
namespace NlsGge.GKDefinitionDesign

theorem KSN021_main (N : ℕ) (hN : 1 ≤ N) :
  AnalyticOnNhd ℝ (inverseSmoothing N) Set.univ ∧
  (∀ z : SobolevCarrier38 (N : ℝ),
    fourierSeq38 (physicalInverseBirkhoff (sequenceSobolevEmbed N z) -
      reflectedFourierL2.symm (sequenceSobolevEmbed N z)) ∈ seqSobolev38 ((N : ℝ) + 1) ∧
    physicalSobolevEmbedRealExponent ((N : ℝ) + 1) (by positivity) (inverseSmoothing N z) =
      physicalInverseBirkhoff (sequenceSobolevEmbed N z) -
        reflectedFourierL2.symm (sequenceSobolevEmbed N z)) ∧
  (∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, 0 ≤ C ∧
    ∀ z : SobolevCarrier38 (N : ℝ), ‖z‖ ≤ B → ‖inverseSmoothing N z‖ ≤ C) :=
  KSN021_main_of N hN (NlsGge.ThirdConsultation.M.molnar_inverse_birkhoff N hN)

end NlsGge.GKDefinitionDesign
