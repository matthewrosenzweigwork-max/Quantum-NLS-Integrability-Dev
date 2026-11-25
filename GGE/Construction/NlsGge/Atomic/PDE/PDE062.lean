import Mathlib
import NlsGge.Atomic.PDE.PDE058
import NlsGge.ThirdConsultation.PDE.Round14ActionFreq
import NlsGge.ThirdConsultation.PDE.PDE062Core
import NlsGge.Atomic.G6.G6033
import NlsGge.Atomic.G6.G6035

                                                                                                                
                                                                                                                     
                                                                                                               
                                                                                                          
                                                                                                               
                                                                                                                      
                                                                                                                          
                                                                                                                    
                                                                                                               
set_option autoImplicit false
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.Common NlsGge.GKDefinitionDesign NlsGge.NLS38
namespace NlsGge.ThirdConsultation.PDE

theorem actual_nls_coordinate_field
    (u : PhysicalSobolev38 ((3 : ℕ) : ℝ)) (n : ℤ) :
  let z : SobolevCarrier38 ((1 : ℕ) : ℝ) := birkhoffSobolev 1 (physicalCoreBase u)
  carrierCoe38 ((1 : ℕ) : ℝ)
    (DPhi 1 (physicalCoreBase u) (nlsVectorField u)) n =
      -Complex.I *
        (actualOmega n (fun k : ℤ => ‖carrierCoe38 ((1 : ℕ) : ℝ) z k‖^2) : ℂ) *
        carrierCoe38 ((1 : ℕ) : ℝ) z n := by
  intro z
  have hz := raw_actions_mem z
  unfold actualOmega
  rw [dif_pos hz, raw_actions_eq z]
  unfold actionFrequency
  exact coord_field_of transformedNLSHamiltonian z _
    ((G6033.1 z (Set.mem_univ _)).differentiableAt) G6035.2.1
    (fun v hv => actual_nls_coordinate_pairing u v hv) _
    (chosenActionExtension_spec _) n

end NlsGge.ThirdConsultation.PDE
