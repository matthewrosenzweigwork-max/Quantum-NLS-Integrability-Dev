import NlsGge.ThirdConsultation.G6.SobolevBirkhoffCompatCore
import NlsGge.Atomic.G6.G6013
import NlsGge.Atomic.G6.G6023

                                                                                                                  
                                                                                                   
                                                                                                     
                                                                                                                  
                                                                                                                 
                                                                                                                 
set_option autoImplicit false
noncomputable section
open scoped Classical
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.Common NlsGge.GK38

namespace NlsGge.GKDefinitionDesign

theorem birkhoffSobolev_mem (m : ℕ)
    (u : PhysicalSobolev38 (m : ℝ)) :
  (physicalBirkhoff (physicalSobolevEmbed m u) : ℤ → ℂ) ∈
    seqSobolev38 (m : ℝ) :=
  SobolevBirkhoffCompatCore.birkhoffSobolev_mem_of G6023 m u

theorem inverseBirkhoffSobolev_mem (m : ℕ)
    (z : SobolevCarrier38 (m : ℝ)) :
  fourierSeq38 (physicalInverseBirkhoff (sequenceSobolevEmbed m z)) ∈
    seqSobolev38 (m : ℝ) :=
  SobolevBirkhoffCompatCore.inverseBirkhoffSobolev_mem_of G6013.2.2.2.2.2 G6023 m z

theorem birkhoffSobolev_coe (m : ℕ)
    (u : PhysicalSobolev38 (m : ℝ)) :
  sequenceSobolevEmbed m (birkhoffSobolev m u) =
    physicalBirkhoff (physicalSobolevEmbed m u) :=
  SobolevBirkhoffCompatCore.birkhoffSobolev_coe_of G6023 m u

theorem inverseBirkhoffSobolev_embed (m : ℕ)
    (z : SobolevCarrier38 (m : ℝ)) :
  physicalSobolevEmbed m (inverseBirkhoffSobolev m z) =
    physicalInverseBirkhoff (sequenceSobolevEmbed m z) :=
  SobolevBirkhoffCompatCore.inverseBirkhoffSobolev_embed_of G6013.2.2.2.2.2 G6023 m z

theorem birkhoffSobolev_inverse_compatible_all (m : ℕ) :
  Function.LeftInverse (inverseBirkhoffSobolev m) (birkhoffSobolev m) ∧
  Function.RightInverse (inverseBirkhoffSobolev m) (birkhoffSobolev m) ∧
  (∀ u : PhysicalSobolev38 (m : ℝ),
    (physicalBirkhoff (physicalSobolevEmbed m u) : ℤ → ℂ) ∈
      seqSobolev38 (m : ℝ) ∧
    sequenceSobolevEmbed m (birkhoffSobolev m u) =
      physicalBirkhoff (physicalSobolevEmbed m u)) ∧
  (∀ z : SobolevCarrier38 (m : ℝ),
    fourierSeq38 (physicalInverseBirkhoff (sequenceSobolevEmbed m z)) ∈
      seqSobolev38 (m : ℝ) ∧
    physicalSobolevEmbed m (inverseBirkhoffSobolev m z) =
      physicalInverseBirkhoff (sequenceSobolevEmbed m z)) :=
  SobolevBirkhoffCompatCore.birkhoffSobolev_inverse_compatible_all_of
    G6013.2.2.2.2.1 G6013.2.2.2.2.2 G6023 m

end NlsGge.GKDefinitionDesign

end
