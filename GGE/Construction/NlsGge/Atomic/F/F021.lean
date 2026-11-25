import NlsGge.Hierarchy.GaussianTailContractionsF06C2_38
import NlsGge.Birkhoff.F05Identity38

                                                                                                          
                                                                                                
                                                                                                 
                                                                                              
                                                                                                  
                                                                                 
                                                                                        
                                               

set_option autoImplicit false
noncomputable section

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.HierarchyRiccati.Core
open NlsGge.Birkhoff

namespace NlsGge.ThirdConsultation.F

theorem f021 (m : ℕ) (hm : 2 ≤ m) (β : ℕ → ℝ)
    (hβ : ∀ j ≤ m, 0 < β j) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ N : ℕ, 1 ≤ N → ∀ z : FourierPlane N,
      Integrable (fun s => Vm38 m β
        (planeElement38 ((m - 1 : ℕ) : ℝ) N z + tailRealization38 m N s))
        (gammaM38 m β) ∧
      |contractionCorrection38 m β N z| ≤
        A * (((N : ℝ) ^ (2 * m))⁻¹ +
          ∑ l ∈ Finset.Icc 1 m, (‖planeL2 N z‖ ^ 2 / (N : ℝ)) ^ l) ∧
      A * (((N : ℝ) ^ (2 * m))⁻¹ +
        ∑ l ∈ Finset.Icc 1 m, (‖planeL2 N z‖ ^ 2 / (N : ℝ)) ^ l) ≤
        B / (N : ℝ) * (1 + (‖planeL2 N z‖ ^ 2) ^ m) := by
  obtain ⟨A, B, hA, hB, h⟩ := contractions_massBound38 hm (fun i hi => (hβ i hi).le)
    (hβ 0 (Nat.zero_le _)) (hβ m le_rfl)
  exact ⟨A, B, hA, hB, h⟩

end NlsGge.ThirdConsultation.F

end
