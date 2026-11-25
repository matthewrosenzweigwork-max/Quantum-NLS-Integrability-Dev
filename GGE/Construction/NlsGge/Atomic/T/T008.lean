import Mathlib
import NlsGge.Hierarchy.A01Spectral38
import NlsGge.Hierarchy.ExponentialH2Moment38
import NlsGge.ThirdConsultation.Common.FiniteSupport
import NlsGge.ThirdConsultation.T.TDefsHost
import NlsGge.ThirdConsultation.T.ECarrier98
import NlsGge.Atomic.T.T005
import NlsGge.Atomic.T.T008Core
import NlsGge.ThirdConsultation.I.ActualEnsembleBridge
import NlsGge.ThirdConsultation.I.LimitLaws
import NlsGge.ThirdConsultation.PDE.BirkhoffRealization
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.ThirdConsultation.R.R109Host
import NlsGge.Weights.Entire

                                                                                                              
                                                                                         
                                                                                                         
                                                                                                                
                                                                                                                       
                                                                                                                    
                                                                                                                   
                                             
                                                                                                
                                                                                                                   
                                                                                                                    
                                                                                                                       
                                                                                                                
                                                                                                                    
                                                                                                        
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped ENNReal Topology BigOperators ContDiff
open NlsGge.Pilot NlsGge.Measure NlsGge.Weights NlsGge.Sobolev38
open NlsGge.Birkhoff NlsGge.HierarchyRiccati.Core
open NlsGge.ThirdConsultation.Common
open scoped BoundedContinuousFunction

namespace NlsGge.ThirdConsultation.T
noncomputable section

theorem ZW_eq_actual (lo up : ℝ) (c : BoundedCoefficients lo up) :
    ZW c = PDE.actualBirkhoffInput38.ZW38 c.val :=
  (I.actual_ensemble_eq_I lo up c).1.symm

/-- Pro T.lean.md L330: the physical pushforward of `muWE` is the actual limit law `I.physicalLaw (weight c.val)`
(= the bodies of `physicalInclusion c s` and `muW c`). -/
theorem muWE_map_physicalLaw (lo up : ℝ) (c : BoundedCoefficients lo up)
    (s : ℝ) (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) :
    (muWE c s hs hs').map (physOfE38 c s) = I.physicalLaw (weight c.val) := by
  have h : (muWE c s hs hs').map (physOfE38 c s) = PDE.actualBirkhoffInput38.muW38 c.val :=
    NlsGge.Atomic.T.T008Core.map_eq PDE.actualBirkhoffInput38 PDE.actualOneSmoothingInput38 c s hs hs'
      (R.canonicalDelta c s hs (le_one_of_lt_three_quarters_W06_38 hs'))
      (R.canonicalDelta_spec c s hs (le_one_of_lt_three_quarters_W06_38 hs')) (ZW c) (ZW_eq_actual lo up c)
  rw [h]
  exact (I.actual_ensemble_eq_I lo up c).2.2.1

theorem fullFourier_unnormalized_test_limit
    (lo up : ℝ) (c : BoundedCoefficients lo up)
    (s : ℝ) (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4)
    (F : ECarrier38 c s →ᵇ ℝ) :
    Integrable F (muWE c s hs hs') ∧
    Tendsto (fun N : ℕ => unnormalizedTest c s F N) atTop
      (𝓝 (ZW c * ∫ x, F x ∂muWE c s hs hs')) := by
  have _hpush := muWE_map_physicalLaw lo up c s hs hs'
  exact NlsGge.Atomic.T.T008Core.limit PDE.actualBirkhoffInput38 PDE.actualOneSmoothingInput38 c s hs hs'
    (R.canonicalDelta c s hs (le_one_of_lt_three_quarters_W06_38 hs'))
    (R.canonicalDelta_spec c s hs (le_one_of_lt_three_quarters_W06_38 hs')) (ZW c) (ZW_eq_actual lo up c) F

end
end NlsGge.ThirdConsultation.T
