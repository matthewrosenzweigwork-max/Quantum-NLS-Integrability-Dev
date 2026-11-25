import Mathlib
import NlsGge.Atomic.G6.G6016Host
import NlsGge.Atomic.G6.G6016Sup1Core
import NlsGge.Atomic.G6.G6016Sup2
import NlsGge.Atomic.G6.G6013
import NlsGge.Atomic.G6.G6014

                                                                                                             
                                                                                                                                
                                                                                                                      
                                                                                                                      
                                                                                                                            
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Atomic.Common
open scoped ENNReal InnerProductSpace

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G6016 (n : ℤ) (u : PhysicalL2) :
  (fun t : ℝ => physicalInverseBirkhoff
    (rotateOneCoordinate n t (physicalBirkhoff u))) 0 = u ∧
  ∀ t : ℝ, HasDerivAt
    (fun s : ℝ => physicalInverseBirkhoff
      (rotateOneCoordinate n s (physicalBirkhoff u)))
    (physicalHamiltonianField (fun v => actualGapActionAllE02_38 v n)
      (physicalInverseBirkhoff (rotateOneCoordinate n t (physicalBirkhoff u)))) t :=
  G6016Aux.core16 fderiv_physicalBirkhoff_actionField G6013.2.2.2.2.1 G6013.2.2.2.2.2
    G6014.2.2.2.1 n u

end
end NlsGge.GKDefinitionDesign
