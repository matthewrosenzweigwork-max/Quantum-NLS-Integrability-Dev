import Mathlib
import NlsGge.ThirdConsultation.G6.SobolevBirkhoffCompatCore
import NlsGge.Atomic.G2.G2045SupB2
import NlsGge.ThirdConsultation.KSPS.Round5

                                                                                                                    
                                                                                                            
                                                                                                                      
                                                                                                                         
                                                                                                                      
                                                                                                                  
                                                                                                                
set_option autoImplicit false
open NlsGge.Pilot NlsGge.GK38 NlsGge.Birkhoff NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation

namespace NlsGge.ThirdConsultation.M016SM

theorem smooth_lift (u : PhysicalL2)
    (hall : ∀ m : ℕ, fourierSeq38 u ∈ seqSobolev38 (m : ℝ)) (N : ℕ) :
    ∃ φ : KSPS.SobolevC N, KSPS.toPotPair φ = realSlice u := by
  have h1 := hall N
  have h2 : fourierSeq38 (star u : PhysicalL2) ∈ seqSobolev38 (N : ℝ) :=
    (mem_seqSobolev38_iff _ _).2 (g2045b_psob_star (N : ℝ) u ((mem_seqSobolev38_iff _ _).1 h1))
  refine ⟨(physicalSobolevRecover N u, physicalSobolevRecover N (star u)), ?_⟩
  rw [realSlice_apply]
  exact Prod.ext ((physicalSobolevEmbed_recover N).2 u h1) ((physicalSobolevEmbed_recover N).2 _ h2)

end NlsGge.ThirdConsultation.M016SM
