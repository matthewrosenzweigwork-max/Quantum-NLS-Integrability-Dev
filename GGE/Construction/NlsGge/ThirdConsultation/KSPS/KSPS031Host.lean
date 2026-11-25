import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS015Host

                                                                                            
                                                                                                    
                                                                                      
                                                                                               
                                                                       
                                                                                                            
                                                                                                       
                                                                                               
                                                                                           
                                                                                                                 
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology BigOperators
open NlsGge.Pilot NlsGge.GK38 NlsGge.GKDefinitionDesign
open NlsGge.Atomic.Common NlsGge.ThirdConsultation
open NlsGge.ThirdConsultation.KSPSRiccati

namespace NlsGge.ThirdConsultation.KSPSWKB
noncomputable section
open NlsGge.ThirdConsultation.KSPS

def halfNode (j : ℤ) : ℂ :=
  ((j : ℂ) + (1 / 2 : ℂ)) * (Real.pi : ℂ)

def NonresonantBranchDomain {N : ℕ} (φ : SobolevC N)
    (j : ℤ) (z : ℂ) : Prop :=
  ‖z - halfNode j‖ < Real.pi / 4 ∧
    ‖discriminant φ z / 2‖ < 1 / 2

def primitive (N : ℕ) (φ : SobolevC N)
    (p : {p : ℤ × ℂ // NonresonantBranchDomain φ p.1 p.2}) : ℂ :=
  let w := Complex.I * (-1 : ℂ) ^ p.1.1 *
    discriminant φ p.1.2 / 2;
  -Complex.I * halfNode p.1.1 +
    Complex.log (w + Complex.sqrt (1 + w ^ 2))

end
end NlsGge.ThirdConsultation.KSPSWKB
