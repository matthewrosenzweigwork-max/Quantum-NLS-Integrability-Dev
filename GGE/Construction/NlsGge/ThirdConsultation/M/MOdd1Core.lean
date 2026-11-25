import Mathlib
import NlsGge.Atomic.M.M053
import NlsGge.ThirdConsultation.G1.Round6
import NlsGge.Hierarchy.RiccatiUnitPeriodIntervalToPhysicalHaar

                                                                                  
                                                                                                                 
                                                                                                      
                                                                                                             
                                                                        
                                                                                                       
                                                                                                                   
                                                                                                                    
                                                                     
                                                                                                        
set_option autoImplicit false

open MeasureTheory
open NlsGge.Pilot NlsGge.GK38 NlsGge.GKDefinitionDesign

namespace NlsGge.ThirdConsultation.MOdd
noncomputable section

theorem hierarchyCharge_eq_hamiltonian {N : ℕ} (φ : NlsGge.ThirdConsultation.KSPS.SobolevC N)
    (k : ℕ) (hk2 : 2 ≤ k) (hkN : k ≤ N + 1) :
    NlsGge.ThirdConsultation.M.hierarchyCharge φ ⟨k, by omega, hkN⟩ =
      hierarchyHamiltonian k (NlsGge.ThirdConsultation.KSPS.toPotPair φ) := by
  have h1 := NlsGge.ThirdConsultation.M.WKB_hierarchy_coefficients_complex N φ k (by omega) hkN
  rw [if_neg (by omega)] at h1
  have h2 : NlsGge.ThirdConsultation.M.hierarchyCharge φ ⟨k, by omega, hkN⟩ =
      NlsGge.ThirdConsultation.KSPS.integralRiccatiCoefficient φ k := by
    rw [h1]; rfl
  rw [h2]
  have hk1 : k ≠ 1 := by omega
  unfold hierarchyHamiltonian
  rw [if_neg hk1]
  show (∫ x in (0 : ℝ)..1, (NlsGge.ThirdConsultation.KSPS.toPotPair φ).1 x *
      NlsGge.ThirdConsultation.KSPS.riccatiLeft φ k x) = _
  have h3 : NlsGge.ThirdConsultation.KSPS.riccatiLeft φ k =
      wkbR (NlsGge.ThirdConsultation.KSPS.toPotPair φ) k := rfl
  rw [h3]
  exact NlsGge.HierarchyRiccati.unitIntervalIntegral_lift_eq_spatialHaar
    (fun x => (NlsGge.ThirdConsultation.KSPS.toPotPair φ).1 x *
      wkbR (NlsGge.ThirdConsultation.KSPS.toPotPair φ) k x)

end
end NlsGge.ThirdConsultation.MOdd
