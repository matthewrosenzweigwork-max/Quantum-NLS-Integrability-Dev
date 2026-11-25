import Mathlib
import NlsGge.ThirdConsultation.M.M053Host

                                                                                                             
                                                                                                             
                                                                                                                  
                                                                                                                      
                                                                                                                     
                                                                                                                     
                                                                                                                
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators

namespace NlsGge.ThirdConsultation.M
noncomputable section

theorem hierarchyCharge_eq_body {N : ℕ} (φ : NlsGge.ThirdConsultation.KSPS.SobolevC N)
    (k : NlsGge.ThirdConsultation.MRiccati.HierarchyIndex N) :
    hierarchyCharge φ k =
      if k.1 = 1 then
        ∫ x in (0 : ℝ)..1,
          NlsGge.GK38.coverRep38 (NlsGge.ThirdConsultation.KSPS.toPotPair φ).1 x *
          NlsGge.GK38.coverRep38 (NlsGge.ThirdConsultation.KSPS.toPotPair φ).2 x
      else
        ∫ x in (0 : ℝ)..1,
          NlsGge.GK38.coverRep38 (NlsGge.ThirdConsultation.KSPS.toPotPair φ).1 x *
          NlsGge.HierarchyRiccati.Core.polynomialEvaluation
            (fun v : NlsGge.HierarchyRiccati.Core.Jet =>
              NlsGge.GK38.coverRep38
                ((NlsGge.GKDefinitionDesign.weakDerivative^[v.2])
                  (if v.1 then (NlsGge.ThirdConsultation.KSPS.toPotPair φ).2
                   else (NlsGge.ThirdConsultation.KSPS.toPotPair φ).1)) x)
            (NlsGge.HierarchyRiccati.Core.p k.1) := rfl

theorem hierarchyCharge_lift
    {N N' : ℕ} (φ : KSPS.SobolevC N) (φ' : KSPS.SobolevC N')
    (h : KSPS.toPotPair φ = KSPS.toPotPair φ')
    (k : ℕ) (hk : 1 ≤ k)
    (hkN : k ≤ N + 1) (hkN' : k ≤ N' + 1) :
    hierarchyCharge φ ⟨k, hk, hkN⟩ =
      hierarchyCharge φ' ⟨k, hk, hkN'⟩ := by
  rw [hierarchyCharge_eq_body, hierarchyCharge_eq_body, h]

end
end NlsGge.ThirdConsultation.M
