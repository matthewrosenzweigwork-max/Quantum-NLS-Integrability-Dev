import Mathlib
import NlsGge.Atomic.KST.KST065
import NlsGge.Atomic.PhysicalSobolev
import NlsGge.Definitions.PilotInterfaces
import NlsGge.GK38.Defs
import NlsGge.ThirdConsultation.KO.Basic
import NlsGge.ThirdConsultation.KST.KST061Host
import NlsGge.ThirdConsultation.KST.KST066Host
import NlsGge.ThirdConsultation.KST.KST066Support

                                                                                                        
                                                                                                    
                                                                                                                    
                                                                                              
                                                                                                  
                                                                                                  
                                                                                 
set_option autoImplicit false
noncomputable section
open Filter Topology
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.ThirdConsultation.KST

theorem kst066 (s : ℝ) (hs : 0 ≤ s)
    (u : NlsGge.Atomic.Common.PhysicalSobolev38 s) :
  ∃ v : ℕ → NlsGge.Atomic.Common.PhysicalSobolev38 s,
    Tendsto v atTop (𝓝 u) ∧
    ∀ j : ℕ, let uj := NlsGge.GKDefinitionDesign.physicalSobolevEmbedRealExponent s hs (v j)
      NlsGge.ThirdConsultation.finiteGap uj ∧ pairFiniteGap (realSlice uj) ∧
      NlsGge.ThirdConsultation.KO.SmoothPhysical uj :=
  kst066_of_smooth (fun w hw => (kst065 w hw).2.1) s hs u

end NlsGge.ThirdConsultation.KST
end
