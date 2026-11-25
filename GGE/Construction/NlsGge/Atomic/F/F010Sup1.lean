import Mathlib
import NlsGge.Atomic.F.F010Host
import NlsGge.Atomic.G6.G6027
import NlsGge.Atomic.G6.G6024Sup2Core
import NlsGge.ThirdConsultation.G6.SobolevBirkhoffCompatCore
import NlsGge.NLS38.PhysicalFlow38

                                                                                                 
                                                                                                            
                                                                                                  
                                                                                                      
                                                                                                     
                                                                                                      
                                                                                                          
                                                                                              
                                                                                               
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.HierarchyRiccati.Core
open NlsGge.SpectralFoundations NlsGge.Birkhoff
open NlsGge.Atomic.Common NlsGge.GKDefinitionDesign

namespace NlsGge.ThirdConsultation.F010Aux

theorem continuous_inverseOnSobolev (m : ℕ) (hm : 2 ≤ m) :
    Continuous (NlsGge.ThirdConsultation.F.inverseOnSobolev m) := by
  have hk : 1 ≤ m - 1 := by omega
  have hc : Continuous (inverseBirkhoffSobolev (m - 1)) :=
    continuousOn_univ.mp (G6027 (m - 1) hk).2.1.continuousOn
  exact (continuous_FinvH38 m).comp ((continuous_ofCarrier38 _).comp
    ((physicalSobolevFourierEquiv38 ((m - 1 : ℕ) : ℝ)).continuous.comp
      (hc.comp (continuous_toCarrier38 _))))

theorem sobolevToL2_inverseOnSobolev (m : ℕ) (w : Hm1 m) :
    sobolevToL2_38 (m - 1) (NlsGge.ThirdConsultation.F.inverseOnSobolev m w) =
      physicalSobolevEmbed (m - 1) (inverseBirkhoffSobolev (m - 1) (toCarrier38 _ w)) := by
  apply NlsGge.NLS38.physicalFourier_injective38
  funext j
  rw [sobolevToL2_38_fourier]
  have h1 := NlsGge.ThirdConsultation.G6024S.fourierSeq38_eq
    (physicalSobolevEmbed (m - 1) (inverseBirkhoffSobolev (m - 1) (toCarrier38 _ w))) (-j)
  rw [physicalSobolevEmbed_fourier, neg_neg] at h1
  change -(carrierCoe38 ((m - 1 : ℕ) : ℝ) (physicalSobolevFourierEquiv38 ((m - 1 : ℕ) : ℝ)
    (inverseBirkhoffSobolev (m - 1) (toCarrier38 _ w))) (-j)) = _
  rw [h1, neg_neg]

theorem physicalBirkhoff_inverseOnSobolev (m : ℕ) (hm : 2 ≤ m) (w : Hm1 m) (n : ℤ) :
    physicalBirkhoff (sobolevToL2_38 (m - 1) (NlsGge.ThirdConsultation.F.inverseOnSobolev m w)) n =
      (show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from w) n := by
  have hk : 1 ≤ m - 1 := by omega
  obtain ⟨-, -, -, hR, hfwd, -⟩ := G6027 (m - 1) hk
  have hC : physicalBirkhoff (physicalSobolevEmbed (m - 1)
      (inverseBirkhoffSobolev (m - 1) (toCarrier38 _ w))) =
      sequenceSobolevEmbed (m - 1) (toCarrier38 _ w) := by
    rw [← (hfwd (inverseBirkhoffSobolev (m - 1) (toCarrier38 _ w))).2, hR (toCarrier38 _ w)]
  rw [sobolevToL2_inverseOnSobolev, hC]
  exact congrFun (sequenceSobolevEmbed_coe (m - 1) (toCarrier38 _ w)) n

end NlsGge.ThirdConsultation.F010Aux
