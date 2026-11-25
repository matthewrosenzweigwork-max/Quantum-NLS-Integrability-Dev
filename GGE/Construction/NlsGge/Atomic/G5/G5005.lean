import Mathlib
import NlsGge.Atomic.G5.G5004
import NlsGge.Atomic.G5.G5005Host
import NlsGge.ThirdConsultation.G5.G5005Support1
import NlsGge.ThirdConsultation.G5.G5005Support2
import NlsGge.ThirdConsultation.G5.G5005Support3
import NlsGge.ThirdConsultation.G5.G5005Support4
import NlsGge.ThirdConsultation.G5.G5005Support5

                                                                                                                  
                                                                                                            
                                                                                                               
                                                                                                               
                                                        
set_option autoImplicit false

open Set Filter Topology Metric
open NlsGge.Pilot NlsGge.GK38
open NlsGge.ThirdConsultation (finiteGap)

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G5005 (u : PhysicalL2) (hu : finiteGap u) :
  let φ := realSlice u
  Memℓp (fun n : ℤ => pairGradientNorm (pairGradient (fun ψ => tauN ψ n) φ)) 2 ∧
  Memℓp (fun n : ℤ => pairGradientNorm
    (pairGradient (fun ψ => muSeq ψ n) φ -
      (1 / 2 : ℂ) • (fourierMode 1 n + fourierMode (-1) n))) 2 ∧
  Memℓp (fun n : ℤ => pairGradientNorm
    (antiDiscrim φ (muSeq φ n) • pairGradient (radiusQuotient n) φ)) 2 ∧
  Memℓp (fun n : ℤ => pairGradientNorm
    ((radiusQuotient n φ * deriv (antiDiscrim φ) (muSeq φ n)) •
      pairGradient (fun ψ => muSeq ψ n) φ)) 2 ∧
  Memℓp (fun n : ℤ => pairGradientNorm
    (radiusQuotient n φ • pairGradient (fun ψ => antiDiscrim ψ (muSeq φ n)) φ -
      (Complex.I / 2) • (fourierMode 1 n - fourierMode (-1) n))) 2 := by
  intro φ
  have hφ : φ ∈ gkW := realSlice_mem_gkW u
  obtain ⟨hq1, -⟩ := G5004 u hu
  have hq : Summable (fun n : ℤ =>
      ‖radiusQuotient n (realSlice u) - radiusQuotientLeading n‖ ^ 2) := by
    have h := (memℓp_gen_iff (by simp)).mp hq1
    simpa using h
  have h2 := NlsGge.ThirdConsultation.G5005Support2.part2 φ hφ
  exact ⟨NlsGge.ThirdConsultation.G5005Support2.part1 φ hφ, h2,
    NlsGge.ThirdConsultation.G5005Support5.part3 u hu,
    NlsGge.ThirdConsultation.G5005Support5.part4 u hq h2,
    NlsGge.ThirdConsultation.G5005Support4.part5 u hq⟩

end
end NlsGge.GKDefinitionDesign
