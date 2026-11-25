import Mathlib
import NlsGge.Birkhoff.S01Equivariance38c
import NlsGge.ThirdConsultation.PDE.BirkhoffTop

                                                                                                                
                                                                                                  
                                                                                                                   
                                                                                                                       
                                              
                                                                                                                       
                                                               
                                                                                                                       
                                                                                                                   
                                                                                                                
                                                                                                                              
set_option autoImplicit false
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.SpectralFoundations NlsGge.Atomic.Common
open NlsGge.GKDefinitionDesign
namespace NlsGge.ThirdConsultation.PDE

theorem actual_momentum_T (x : ℤ → ℂ)
    (hx : x ∈ seqSobolev38 ((1 : ℕ) : ℝ)) :
  momSeq38 (NlsGge.ThirdConsultation.PDE.actualBirkhoffTop38.T x) = momSeq38 x :=
  NlsGge.Birkhoff.BirkhoffTop38.momSeq38_T actualBirkhoffTop38 x hx

end NlsGge.ThirdConsultation.PDE
