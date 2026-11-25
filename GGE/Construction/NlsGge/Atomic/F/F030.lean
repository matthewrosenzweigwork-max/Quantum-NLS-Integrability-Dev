import Mathlib
import NlsGge.Atomic.F.F030Host
import NlsGge.Birkhoff.F08Bare38f

                                                                                                               
                                                                                                                        
                                                                                                                      
                                                                                                    
                                                                                  
                                                                                                   
                                                                                                      
                                                                                                           
                                                           
                                                                                          
                                                                                                           
                                                                                   
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology ContDiff
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.HierarchyRiccati.Core
open NlsGge.SpectralFoundations NlsGge.Birkhoff NlsGge.Measure

namespace NlsGge.ThirdConsultation.F

theorem f030 (m : ℕ) (hm : 2 ≤ m) (β : ℕ → ℝ)
    (hβ : ∀ j ≤ m, 0 < β j) :
    ∀ N : ℕ,
      (∀ z : FourierPlane N, β 0 * ‖planeL2 N z‖ ^ 2 ≤ EmPlane38 m β N z) ∧
      Integrable (fun z : FourierPlane N => Real.exp (-EmPlane38 m β N z))
        (finiteComplexVolume (Fin (2 * N + 1))) ∧
      0 < ZcalBare38 m β N ∧
      Integrable (weightFN38 m β N) (gammaFM38 m β) ∧
      (∫ u, weightFN38 m β N u ∂gammaFM38 m β) = finiteOrderRelativeZ m β N ∧
      IsProbabilityMeasure (nuBare38 m β N) ∧
      (∀ L : ℕ, UniformIntegrable
        (fun k : Fin (L + 1) => weightFN38 m β k.val) 1 (gammaFM38 m β)) := by
  intro N
  refine ⟨fun z => ?_, integrable_expEm38 hm hβ N, ZcalBare_pos38 hm hβ N,
    ?_, ?_, isProbabilityMeasure_nuBare38 hm hβ N, fun L => ?_⟩
  · rw [planeL2_norm_sq]
    exact EmPlane_ge38 hm hβ N z
  · exact (integrable_gammaF_iff38 hm hβ _ (measurable_weightFN38 m β N)).2
      ((integrable_weightN38 hm hβ N).congr (ae_weightN_eq38 hm hβ N))
  · rw [integral_gammaF38 hm hβ _ (measurable_weightFN38 m β N), finiteOrderRelativeZ,
      ZcalBare_rel38 hm hβ N]
    exact (integral_congr_ae (ae_weightN_eq38 hm hβ N)).symm
  · refine uniformIntegrable_finite le_rfl ENNReal.one_ne_top fun k => ?_
    exact memLp_one_iff_integrable.2
      ((integrable_gammaF_iff38 hm hβ _ (measurable_weightFN38 m β k.val)).2
        ((integrable_weightN38 hm hβ k.val).congr (ae_weightN_eq38 hm hβ k.val)))

end NlsGge.ThirdConsultation.F
