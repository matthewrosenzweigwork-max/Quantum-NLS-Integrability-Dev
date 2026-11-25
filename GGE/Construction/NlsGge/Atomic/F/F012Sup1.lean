import Mathlib
import NlsGge.Atomic.F.F012Host
import NlsGge.Atomic.G6.G6027
import NlsGge.Atomic.G6.G6024Sup2Core
import NlsGge.ThirdConsultation.G6.SobolevBirkhoffCompatCore
import NlsGge.NLS38.PhysicalFlow38

                                                                                                 
                                                                                              
                                                                                                                     
                                                                                                            
                                                                                                         
                                                                                                         
set_option autoImplicit false
noncomputable section
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.HierarchyRiccati.Core
open NlsGge.SpectralFoundations NlsGge.Birkhoff
open NlsGge.Atomic.Common NlsGge.GKDefinitionDesign

namespace NlsGge.ThirdConsultation.F012Aux

theorem sobolevToL2_FinvH (m : ℕ) (x : Hm1 m) :
    sobolevToL2_38 (m - 1) (FinvH38 m x) =
      physicalSobolevEmbed (m - 1)
        ((physicalSobolevFourierEquiv38 ((m - 1 : ℕ) : ℝ)).symm (toCarrier38 _ x)) := by
  apply NlsGge.NLS38.physicalFourier_injective38
  funext j
  rw [sobolevToL2_38_fourier]
  have h1 := NlsGge.ThirdConsultation.G6024S.fourierSeq38_eq
    (physicalSobolevEmbed (m - 1)
      ((physicalSobolevFourierEquiv38 ((m - 1 : ℕ) : ℝ)).symm (toCarrier38 _ x))) (-j)
  rw [physicalSobolevEmbed_fourier, LinearIsometryEquiv.apply_symm_apply, neg_neg] at h1
  change -(carrierCoe38 ((m - 1 : ℕ) : ℝ) (toCarrier38 _ x) (-j)) = _
  rw [h1, neg_neg]

theorem finiteT_coe (m : ℕ) (hm : 2 ≤ m) (x : Hm1 m) (n : ℤ) :
    NlsGge.ThirdConsultation.F.sobolevCoe _ (NlsGge.ThirdConsultation.F.finiteT m x) n =
      physicalBirkhoff (sobolevToL2_38 (m - 1) (FinvH38 m x)) n := by
  have hk : 1 ≤ m - 1 := by omega
  rw [sobolevToL2_FinvH, ← ((G6027 (m - 1) hk).2.2.2.2.1
    ((physicalSobolevFourierEquiv38 ((m - 1 : ℕ) : ℝ)).symm (toCarrier38 _ x))).2]
  exact (congrFun (sequenceSobolevEmbed_coe (m - 1) (birkhoffSobolev (m - 1)
    ((physicalSobolevFourierEquiv38 ((m - 1 : ℕ) : ℝ)).symm (toCarrier38 _ x)))) n).symm

end NlsGge.ThirdConsultation.F012Aux
