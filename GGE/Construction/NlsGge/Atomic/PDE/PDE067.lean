import Mathlib
import NlsGge.ThirdConsultation.PDE.BirkhoffTop
import NlsGge.ThirdConsultation.PDE.BirkhoffRaw
import NlsGge.ThirdConsultation.Common.Actions
import NlsGge.ThirdConsultation.Common.FiniteSupport
import NlsGge.NLS38.PhysicalFlow38
import NlsGge.Atomic.PDE.PDE061
import NlsGge.Atomic.PDE.PDE066

                                                                                                  
                                                                                                                                              
                                                                                                                 
                                                                                                                       
                                                                                                                          
                                                                                                                       
                                                                                                                        
                                                                                                                        
                                                                                                  
                                                                                                                    
                                                                                                
                                      
set_option autoImplicit false
open Set Filter Topology Metric MeasureTheory
open scoped BigOperators ENNReal InnerProductSpace
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.SpectralFoundations NlsGge.GK38 NlsGge.Atomic.Common
open NlsGge.GKDefinitionDesign NlsGge.NLS38
open NlsGge.ThirdConsultation.Common
namespace NlsGge.ThirdConsultation.PDE

def actualBirkhoffNLSFlowInput38 :
    BirkhoffNLSFlowInput38 NlsGge.ThirdConsultation.PDE.actualBirkhoffTop38
      NlsGge.NLS38.nlsFlowL2 where
  rotation := by
    refine ⟨actualOmega, measurable_actualOmega, ?_⟩
    intro u hfin t n
    have hf : FiniteSupportSequence (actualPhi u) := by
      simpa only [FiniteSupportSequence,
        NlsGge.ThirdConsultation.PDE.actualBirkhoffTop38_Phi] using hfin
    have hact : actions (actualPhi u) = fun k => ‖actualPhi u k‖ ^ 2 := rfl
    simp only [NlsGge.ThirdConsultation.PDE.actualBirkhoffTop38_Phi]
    rw [actual_finitegap_rotation u hf t n, hact]
    congr 2
    ring

end NlsGge.ThirdConsultation.PDE
