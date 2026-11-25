import Mathlib
import NlsGge.Atomic.F.F012Core
import NlsGge.Atomic.F.F012Sup1
import NlsGge.Atomic.G6.G6028

                                                                                                               
                                                                                                                 
                                                                                                                       
                                                                                                          
                                                                                                                   
                                                                                                                
                                                                                                                      
                                                                                      
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology ContDiff
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.HierarchyRiccati.Core
open NlsGge.SpectralFoundations NlsGge.Birkhoff NlsGge.Measure

namespace NlsGge.ThirdConsultation.F

theorem f012 (m : ℕ) (hm : 2 ≤ m) (β : ℕ → ℝ)
    (hβ : ∀ j ≤ m, 0 < β j) :
    Continuous (finiteD m β) ∧
    ∀ h : SobolevHilbert (m : ℝ),
      Summable (fun n : ℤ => finiteHierarchyRate38 m β n *
        ‖sobolevCoe _ (lowerSobolev m h) n‖ ^ 2) ∧
      Summable (fun n : ℤ => finiteHierarchyRate38 m β n *
        ‖sobolevCoe _ (finiteT m (lowerSobolev m h)) n‖ ^ 2) ∧
      finiteD m β (lowerSobolev m h) =
        finiteA m β (finiteT m (lowerSobolev m h)) -
          finiteA m β (lowerSobolev m h) :=
  NlsGge.ThirdConsultation.F012Aux.core m hm β hβ
    (fun u n => NlsGge.GKDefinitionDesign.physicalBirkhoff u n)
    (fun u n => (NlsGge.GKDefinitionDesign.G6028.1 u n).2.2)
    (finiteT m) (fun x n => NlsGge.ThirdConsultation.F012Aux.finiteT_coe m hm x n)

end NlsGge.ThirdConsultation.F
