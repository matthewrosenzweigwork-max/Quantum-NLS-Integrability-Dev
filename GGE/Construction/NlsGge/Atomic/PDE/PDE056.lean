import Mathlib
import NlsGge.Birkhoff.S01Equivariance38c
import NlsGge.ThirdConsultation.PDE.BirkhoffTop

                                                                                                                
                                                                                           
                                                                                                        
                                                                                                                         
                                                                                                                     
                                                                                                            
                               
set_option autoImplicit false
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.SpectralFoundations NlsGge.Atomic.Common
open NlsGge.GKDefinitionDesign
namespace NlsGge.ThirdConsultation.PDE

theorem actual_T_Tinv_rotation
    (x z : ℤ → ℂ) (hx : x ∈ seqSobolev38 0) (hz : z ∈ seqSobolev38 0)
    (theta : ℝ) :
  NlsGge.ThirdConsultation.PDE.actualBirkhoffTop38.T (rotSeq38 theta x) =
      rotSeq38 theta (NlsGge.ThirdConsultation.PDE.actualBirkhoffTop38.T x) ∧
  NlsGge.ThirdConsultation.PDE.actualBirkhoffTop38.Tinv (rotSeq38 theta z) =
      rotSeq38 theta (NlsGge.ThirdConsultation.PDE.actualBirkhoffTop38.Tinv z) :=
  ⟨NlsGge.Birkhoff.BirkhoffTop38.T_rotSeq38 actualBirkhoffTop38
      (actualBirkhoffAnalytic38.mono (Set.subset_univ _)) actualBirkhoffCanonical38 x hx theta,
    NlsGge.Birkhoff.BirkhoffTop38.Tinv_rotSeq38 actualBirkhoffTop38
      (actualBirkhoffAnalytic38.mono (Set.subset_univ _)) actualBirkhoffCanonical38 z hz theta⟩

end NlsGge.ThirdConsultation.PDE
