import Mathlib
import NlsGge.ThirdConsultation.G5.G5033Support1
import NlsGge.ThirdConsultation.G5033Host
import NlsGge.Atomic.G5.G5024
import NlsGge.ThirdConsultation.G2.G2071Support1
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
-- MODULE: NlsGge.Atomic.G5.G5033

                                                                                                                            
                                                                                                                             
                                                                                        
                                                                              
                                                                                                           
                                                                                                                
                                                                            
                                                                                                                  
                                                                                        
                                                                                                                     
                                                                                                              
                                                                                                      
set_option autoImplicit false

open Set Filter Topology
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G5033 (u : PhysicalL2) (m n : ℤ)
    (hm : gamma2 (realSlice u) m ≠ 0) (z : ℂ)
    (hz : ∀ k : ℤ, k ≠ n → z ≠ psiRootAt n k (realSlice u)) :
  let φ := realSlice u
  Memℓp (fun k : ℤ => if k = n then 0 else
    pairPoissonCLM (fderiv ℂ (psiRootAt n k) φ) (angleDerivative m φ)) 2 ∧
  Summable (fun k : ℤ => if k = n then 0 else
    pairPoissonCLM (fderiv ℂ (psiRootAt n k) φ) (angleDerivative m φ) /
      (psiRootAt n k φ - z)) ∧
  pairPoissonCLM (fderiv ℂ (psiAt n z) φ) (angleDerivative m φ) =
    psiAt n z φ * ∑' k : ℤ, if k = n then 0 else
      pairPoissonCLM (fderiv ℂ (psiRootAt n k) φ) (angleDerivative m φ) /
        (psiRootAt n k φ - z) := by
  intro φ
  have hF : DifferentiableAt ℂ (sourceF n) (realSlice u) :=
    (G2071S1.structural.2.2.2.1 n (realSlice u)
      (G2071S1.structural.2.1 (Set.mem_range_self u))).differentiableAt
  obtain ⟨h1, h2, h3⟩ := NlsGge.ThirdConsultation.G5033Support1.assembly n (sourceF n) (realSlice u) hF z hz
    (-Complex.I • (pairGradientCLM (angleDerivative m (realSlice u))).2,
      Complex.I • (pairGradientCLM (angleDerivative m (realSlice u))).1)
  exact ⟨h1, h2, h3⟩

end
end NlsGge.GKDefinitionDesign
