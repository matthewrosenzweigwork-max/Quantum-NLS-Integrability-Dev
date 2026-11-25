import NlsGge.ThirdConsultation.PDE.BirkhoffRaw
import NlsGge.ThirdConsultation.G6.SobolevBirkhoffCompatCore

                                                                                                                 
                                                                                                              
                                                                                                                        
                                                                                                                 
                                                                                                                         
                                                                                                                       
                                                               
set_option autoImplicit false
open Set
open scoped Classical ENNReal Topology
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.Common NlsGge.SpectralFoundations
open NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation.Common
namespace NlsGge.ThirdConsultation.PDE
noncomputable section

def actualTC38 (m : ℕ)
    (x : SobolevCarrier38 (m : ℝ)) : SobolevCarrier38 (m : ℝ) :=
  birkhoffSobolev m ((physicalSobolevFourierEquiv38 (m : ℝ)).symm x)

def actualTinvC38 (m : ℕ)
    (z : SobolevCarrier38 (m : ℝ)) : SobolevCarrier38 (m : ℝ) :=
  physicalSobolevFourierEquiv38 (m : ℝ) (inverseBirkhoffSobolev m z)

namespace BirkhoffCarrierCore

theorem t_carrier_eq_of
    (hG : ∀ (u : PhysicalL2) (m : ℕ), fourierSeq38 u ∈ seqSobolev38 (m : ℝ) ↔
      (physicalBirkhoff u : ℤ → ℂ) ∈ seqSobolev38 (m : ℝ))
    (m : ℕ) (hT : ∀ x ∈ seqSobolev38 (m : ℝ), actualT38 x ∈ seqSobolev38 (m : ℝ)) :
    carrierMap38 (m : ℝ) (m : ℝ) actualT38 hT = actualTC38 m := by
  funext x
  apply carrierExt38
  rw [carrierMap38_coe]
  have hx : carrierCoe38 (m : ℝ) x =
      fourierSeq38 (physicalSobolevEmbed m ((physicalSobolevFourierEquiv38 (m : ℝ)).symm x)) := by
    funext n
    rw [physicalSobolevEmbed_fourier, LinearIsometryEquiv.apply_symm_apply]
  rw [hx, actualT38_fourierSeq38]
  show (physicalBirkhoff (physicalSobolevEmbed m ((physicalSobolevFourierEquiv38 (m : ℝ)).symm x)) :
    ℤ → ℂ) = carrierCoe38 (m : ℝ) (actualTC38 m x)
  unfold actualTC38
  rw [← sequenceSobolevEmbed_coe m
      (birkhoffSobolev m ((physicalSobolevFourierEquiv38 (m : ℝ)).symm x)),
    SobolevBirkhoffCompatCore.birkhoffSobolev_coe_of hG]

theorem tinv_carrier_eq_of
    (hR : Function.RightInverse physicalInverseBirkhoff physicalBirkhoff)
    (hG : ∀ (u : PhysicalL2) (m : ℕ), fourierSeq38 u ∈ seqSobolev38 (m : ℝ) ↔
      (physicalBirkhoff u : ℤ → ℂ) ∈ seqSobolev38 (m : ℝ))
    (m : ℕ) (hTinv : ∀ z ∈ seqSobolev38 (m : ℝ), actualTinv38 z ∈ seqSobolev38 (m : ℝ)) :
    carrierMap38 (m : ℝ) (m : ℝ) actualTinv38 hTinv = actualTinvC38 m := by
  funext z
  apply carrierExt38
  rw [carrierMap38_coe]
  have h0 : carrierCoe38 (m : ℝ) z ∈ seqSobolev38 0 :=
    seqSobolev38_natCast_mono (carrierCoe38_mem _ z)
  have hw : seqToLp38 (carrierCoe38 (m : ℝ) z) h0 = sequenceSobolevEmbed m z :=
    lp.ext (sequenceSobolevEmbed_coe m z).symm
  rw [actualTinv38_of_mem _ h0, hw]
  show fourierSeq38 (physicalInverseBirkhoff (sequenceSobolevEmbed m z)) =
    carrierCoe38 (m : ℝ) (actualTinvC38 m z)
  unfold actualTinvC38
  rw [← SobolevBirkhoffCompatCore.inverseBirkhoffSobolev_embed_of hR hG m z]
  funext n
  exact physicalSobolevEmbed_fourier m _ n

end BirkhoffCarrierCore

end
end NlsGge.ThirdConsultation.PDE
