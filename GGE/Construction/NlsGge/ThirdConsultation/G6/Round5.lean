import Mathlib
import NlsGge.ThirdConsultation.Sobolev.Round5
import NlsGge.ThirdConsultation.G1.Round5
import NlsGge.ThirdConsultation.G6.Energy031B

                                                                                                             
                                                      
                                                                                                                               
                                                                                  
set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory
open scoped ENNReal
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.Common NlsGge.GK38
open NlsGge.HierarchyRiccati.Core

local instance : IsProbabilityMeasure spatialMeasure := by
  unfold spatialMeasure
  infer_instance

namespace NlsGge.GKDefinitionDesign

def nlsHamiltonian (u : PhysicalSobolev38 ((1 : ℕ) : ℝ)) : ℝ :=
  (∑' n : ℤ, (2 * Real.pi * (n : ℝ)) ^ 2 *
    ‖fourierSeq38 (physicalSobolevEmbed 1 u) n‖ ^ 2) +
  ∫ x : PhysicalCircle, ‖physicalSobolevEmbed 1 u x‖ ^ 4 ∂spatialMeasure

theorem weakDerivative_physicalSobolevEmbed
    (u : PhysicalSobolev38 ((1 : ℕ) : ℝ)) :
  weakDerivative (physicalSobolevEmbed 1 u) = physicalSobolevDerivative38 1 u := by
  have hd := weakDerivative_domain_of_H1 _ (embed1_physicalSobolev u)
  apply reflectedFourierL2.injective
  apply lp.ext
  funext n
  have h1 := weakDerivative_coeff _ hd n
  have h2 := physicalSobolevDerivative38_reflected 1 u n
  have h3 := physicalSobolevEmbed_fourier 1 u n
  change reflectedFourierL2 (weakDerivative (physicalSobolevEmbed 1 u)) n =
    reflectedFourierL2 (physicalSobolevDerivative38 1 u) n
  rw [h1]
  change _ = fourierSeq38 (physicalSobolevDerivative38 1 u) n
  rw [h2, pow_one]
  change _ * fourierSeq38 (physicalSobolevEmbed 1 u) n = _
  rw [h3]

end NlsGge.GKDefinitionDesign
end
