import Mathlib
import NlsGge.ThirdConsultation.PDE.ActualEnsemble
import NlsGge.ThirdConsultation.PDE.PDE072Sup
import NlsGge.Birkhoff.S04FiniteGapInvariance38

                                                                                                  
                                                                                                                           
                                                                                                                  
                                                                                                                 
                                                                                                                    
                                                                                                          
                
set_option autoImplicit false
open Set Filter Topology Metric MeasureTheory
open scoped BigOperators ENNReal InnerProductSpace
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.SpectralFoundations NlsGge.GK38 NlsGge.Atomic.Common
open NlsGge.GKDefinitionDesign NlsGge.NLS38
open NlsGge.ThirdConsultation.Common
namespace NlsGge.ThirdConsultation.PDE

theorem actual_finiteGapField_twist
    (Lambda : Finset ℤ) (z : Lambda → ℂ) (t : ℝ) :
  nlsFlowL2 t (finiteGapField Lambda z) =
    finiteGapField Lambda
      (NlsGge.NLS38.twist
        (NlsGge.Birkhoff.kappaΛ38 actualOmega Lambda t) z) :=
  NlsGge.Birkhoff.finiteGapField_rotation_of actualBirkhoffTop38 nlsFlowL2 actualOmega
    PDE072Aux.actual_rotation_Phi Lambda z t

end NlsGge.ThirdConsultation.PDE
