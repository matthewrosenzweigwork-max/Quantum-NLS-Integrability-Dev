import Mathlib
import NlsGge.Atomic.PhysicalSobolev
import NlsGge.Atomic.G6.G6002Sup1Core
import NlsGge.Atomic.G6.G6001
import NlsGge.Atomic.G5.G5015
import NlsGge.Atomic.G5.G5016
import NlsGge.Atomic.G4.G4042

                                                                        
                                                                           
                                                                                                                                   
                                                           
                                                                                                                                 
                                                                                                                          
                                                                                                                    
                                                                                                                         
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Atomic.Common
open scoped ENNReal InnerProductSpace

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G6002 (u : PhysicalL2) :
  (∃ e : PhysicalL2 ≃L[ℝ] Lib.L2Z,
    e.toContinuousLinearMap = fderiv ℝ physicalBirkhoff u) ∧
  (∃ e : PhysicalL2 ≃L[ℝ] CartesianReal,
    e.toContinuousLinearMap = fderiv ℝ realBirkhoffCartesian u) := by
  have h1 : ∃ e : PhysicalL2 ≃L[ℝ] Lib.L2Z,
      e.toContinuousLinearMap = fderiv ℝ physicalBirkhoff u :=
    (G5016 u).2 (G6002Aux.adjoint_equiv (jacobianAdjoint u) (G6001 u) (G5015 u))
  exact ⟨h1, G6002Aux.cart_equiv u ((G4042.2.2 u (Set.mem_univ u)).differentiableAt) h1⟩

end
end NlsGge.GKDefinitionDesign
