import Mathlib
import NlsGge.Atomic.F.F010Host
import NlsGge.Atomic.F.F010Core
import NlsGge.Atomic.F.F010Sup1
import NlsGge.Atomic.G6.G6029

                                                                                                               
                                                                                                              
                                                                                                                       
                                                                                                                 
                                                                                                   
                                                                                                         
                                                                                                                    
                                                                              
                                                                                                                   
                                                                            
                                                                                               
                                                                                                               
                                                                                                      
                                                              
                                                                                                       
                                         
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology ContDiff
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.HierarchyRiccati.Core
open NlsGge.SpectralFoundations NlsGge.Birkhoff NlsGge.Measure

namespace NlsGge.ThirdConsultation.F

theorem f010 (m : ℕ) (hm : 2 ≤ m) (β : ℕ → ℝ)
    (hβ : ∀ j ≤ m, 0 < β j) :
    Summable (fun n : ℤ => sobolevModeWeight ((m - 1 : ℕ) : ℝ) n /
      finiteHierarchyRate38 m β n) ∧
    (∀ᵐ z ∂gammaM38 m β,
      Summable (fun n : ℤ => sobolevModeWeight ((m - 1 : ℕ) : ℝ) n * ‖z n‖ ^ 2) ∧
      ∀ n : ℤ, NlsGge.GKDefinitionDesign.physicalBirkhoff
        (sobolevToL2_38 (m - 1) (inverseOnSequence m z)) n = z n) ∧
    (∀ z : ℤ → ℂ, 0 < finiteDensity m β z ∧ finiteDensity m β z ≤ 1) ∧
    Integrable (finiteDensity m β) (gammaM38 m β) ∧
    0 < finiteNormalizer m β ∧ finiteNormalizer m β ≤ 1 ∧
    IsProbabilityMeasure (finiteGapLaw m β) ∧
    (∀ N : ℕ,
      0 < finiteGapNormalizer m β N ∧ finiteGapNormalizer m β N ≤ 1 ∧
      IsProbabilityMeasure (finiteGapApprox m β N) ∧
      ∀ z : ℤ → ℂ,
        NlsGge.ThirdConsultation.finiteGap
          (sobolevToL2_38 (m - 1) (finiteGapField m N z))) ∧
    (∀ᵐ z ∂gammaM38 m β,
      Tendsto (fun N => finiteGapField m N z) atTop (nhds (inverseOnSequence m z))) ∧
    Tendsto (finiteGapNormalizer m β) atTop (nhds (finiteNormalizer m β)) ∧
    ∀ F : BoundedContinuousFunction (Hm1 m) ℝ,
      Tendsto (fun N => ∫ u, F u ∂finiteGapApprox m β N) atTop
        (nhds (∫ u, F u ∂finiteGapLaw m β)) := by
  have hβ' : ∀ i ≤ m, 0 ≤ β i := fun i hi => (hβ i hi).le
  have h0 : 0 < β 0 := hβ 0 (Nat.zero_le m)
  have hM : 0 < β m := hβ m le_rfl
  obtain ⟨hdens, hint, hZ, hZ1, hP, hN, hae, hZt, hw⟩ :=
    NlsGge.ThirdConsultation.F010Aux.core hm hβ (inverseOnSobolev m)
      (NlsGge.ThirdConsultation.F010Aux.continuous_inverseOnSobolev m hm)
  refine ⟨summable_tailRatio38 m β hm hβ' h0 hM, ?_, hdens, hint, hZ, hZ1, hP,
    fun N => ⟨(hN N).1, (hN N).2.1, (hN N).2.2, fun z => ?_⟩, hae, hZt, hw⟩
  · filter_upwards [ae_summable38 hm hβ' h0 hM, ae_gaussianRealization_apply38 hm hβ' h0 hM]
      with z hz hgz
    exact ⟨hz, fun n =>
      (NlsGge.ThirdConsultation.F010Aux.physicalBirkhoff_inverseOnSobolev m hm
        (gaussianRealization38 m z) n).trans (hgz n)⟩
  · refine (NlsGge.GKDefinitionDesign.G6029 _).1.mp
      ((Finset.Icc (-(N : ℤ)) N).finite_toSet.subset fun n hn => ?_)
    by_contra hnot
    apply hn
    have hfid := NlsGge.ThirdConsultation.F010Aux.physicalBirkhoff_inverseOnSobolev m hm
      (PN38 m N z) n
    exact hfid.trans (by
      rw [PN38_coeff, ite_eq_right_iff]
      exact fun h => absurd (Finset.mem_coe.2 h) hnot)

end NlsGge.ThirdConsultation.F
