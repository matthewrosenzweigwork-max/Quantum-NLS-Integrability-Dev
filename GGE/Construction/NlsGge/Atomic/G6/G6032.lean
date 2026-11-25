import Mathlib
import NlsGge.Atomic.G6.G6032Core
import NlsGge.Atomic.G6.G6013
import NlsGge.Atomic.G6.G6021
import NlsGge.Atomic.G6.G6029
import NlsGge.Atomic.G6.G6030
import NlsGge.Atomic.G6.G6031
import NlsGge.Atomic.G2.G2045

                                                                                                                 
                                                                                                               
                                                                                                              
                                                                                                                 
                                                                                                               
                                                                                                         
                                                                                                            
                                   
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Atomic.Common
open scoped ENNReal InnerProductSpace

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G6032 (u v : PhysicalSobolev38 ((1 : ℕ) : ℝ))
    (hiso : physicalSobolevEmbed 1 v ∈ isospectralSet (physicalSobolevEmbed 1 u)) :
  nlsHamiltonian u = nlsHamiltonian v := by
  obtain ⟨U, -, -, hU, -, hall⟩ := G2_045 3 (by norm_num)
  exact NlsGge.ThirdConsultation.G6032S.G6032_of G6013.2.2.2.2.1 G6013.2.2.2.2.2 (fun x => (G6021 x).2)
    (fun x => (G6029 x).2.2) (fun x hx => (G6030 x 1 hx).2.2) G6031.1 (fun w => (G6031.2 w).2.2.2.2)
    U hU (fun φ hφ => ((hall φ hφ).2.2.2 rfl).2) u v hiso

end
end NlsGge.GKDefinitionDesign
