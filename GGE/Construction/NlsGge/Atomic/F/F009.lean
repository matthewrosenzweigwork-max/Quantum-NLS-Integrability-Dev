import Mathlib
import NlsGge.Atomic.F.F009Host
import NlsGge.Atomic.F.F009Core
import NlsGge.Atomic.G6.G6028

                                                                                                               
                                                                                                             
                                                                                                                   
                                                                                                      
                                                                                                             
                                                                                               
                                                                                                       
                                                                                                         
                                                                                                      
                                                                                                             
                                                                                                             
                                                                                              
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology ContDiff
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.HierarchyRiccati.Core
open NlsGge.SpectralFoundations NlsGge.Birkhoff NlsGge.Measure

namespace NlsGge.ThirdConsultation.F

theorem f009 (m : ℕ) (hm : 2 ≤ m) (β : ℕ → ℝ)
    (hβ : ∀ j ≤ m, 0 < β j) (y : SobolevHilbert (m : ℝ)) :
    Summable (fun n : ℤ => finiteHierarchyRate38 m β n *
      ‖NlsGge.GKDefinitionDesign.physicalBirkhoff (sobolevToL2_38 m y) n‖ ^ 2) ∧
    Summable (fun n : ℤ => finiteHierarchyRate38 m β n *
      ‖(show WeightedHilbert (sobolevModeWeight (m : ℝ)) from y) n‖ ^ 2) ∧
    Summable (fun n : ℤ => |gapRemainderTermE02_38 (finiteWeightE02_38 m β)
      (sobolevToL2_38 m y) n|) ∧
    energySobolev38 m β y = actionQuadratic m β (sobolevToL2_38 m y) +
      Rm38 m β (lowerSobolev m y) ∧
    energySobolev38 m β y = fourierQuadratic m β y + Vm38 m β (lowerSobolev m y) :=
  NlsGge.ThirdConsultation.F009Aux.core m hm β hβ
    (fun u n => NlsGge.GKDefinitionDesign.physicalBirkhoff u n)
    (fun u n => (NlsGge.GKDefinitionDesign.G6028.1 u n).2.2) y (lowerSobolev m y)
    (fun n => (NlsGge.ThirdConsultation.F009Aux.lower_coeff m y n).symm)

end NlsGge.ThirdConsultation.F
