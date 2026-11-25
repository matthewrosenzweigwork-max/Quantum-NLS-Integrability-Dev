import Mathlib
import NlsGge.ThirdConsultation.PDE.BirkhoffCarrierCore

                                                                                  
                                                                                                                    
                                                                                                                           
                                                                                                                            
                                                                                                                           
                                                                                                                        
                                                                                                                            
                                                                                                                      
set_option autoImplicit false
open Set
open scoped Classical ENNReal Topology
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.Common NlsGge.SpectralFoundations
open NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation.Common

namespace NlsGge.ThirdConsultation.PDE
namespace BirkhoffTopCore
noncomputable section

theorem continuous_of_analytic {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} (hf : AnalyticOnNhd ℝ f Set.univ) :
    Continuous f :=
  continuous_iff_continuousAt.2 (fun x => (hf x (Set.mem_univ x)).continuousAt)

theorem T_analytic_of
    (hmT : ∀ m : ℕ, ∀ x ∈ seqSobolev38 (m : ℝ), actualT38 x ∈ seqSobolev38 (m : ℝ))
    (hcar : ∀ m : ℕ, carrierMap38 (m : ℝ) (m : ℝ) actualT38 (hmT m) = actualTC38 m)
    (h0 : AnalyticOnNhd ℝ (carrierMap38 ((0 : ℕ) : ℝ) ((0 : ℕ) : ℝ) actualT38 (hmT 0)) Set.univ)
    (hG : ∀ m : ℕ, 1 ≤ m → AnalyticOnNhd ℝ (birkhoffSobolev m) Set.univ) (m : ℕ) :
    AnalyticOnNhd ℝ (carrierMap38 (m : ℝ) (m : ℝ) actualT38 (hmT m)) Set.univ := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact h0
  · rw [hcar m]
    intro x _
    unfold actualTC38
    exact (hG m hm _ (Set.mem_univ _)).comp
      ((physicalSobolevFourierEquiv38 (m : ℝ)).symm.toContinuousLinearEquiv.toContinuousLinearMap.analyticAt x)

theorem Tinv_analytic_of
    (hmTi : ∀ m : ℕ, ∀ z ∈ seqSobolev38 (m : ℝ), actualTinv38 z ∈ seqSobolev38 (m : ℝ))
    (hcar : ∀ m : ℕ, carrierMap38 (m : ℝ) (m : ℝ) actualTinv38 (hmTi m) = actualTinvC38 m)
    (h0 : AnalyticOnNhd ℝ (carrierMap38 ((0 : ℕ) : ℝ) ((0 : ℕ) : ℝ) actualTinv38 (hmTi 0)) Set.univ)
    (hG : ∀ m : ℕ, 1 ≤ m → AnalyticOnNhd ℝ (inverseBirkhoffSobolev m) Set.univ) (m : ℕ) :
    AnalyticOnNhd ℝ (carrierMap38 (m : ℝ) (m : ℝ) actualTinv38 (hmTi m)) Set.univ := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact h0
  · rw [hcar m]
    intro z _
    unfold actualTinvC38
    exact ((physicalSobolevFourierEquiv38 (m : ℝ)).toContinuousLinearEquiv.toContinuousLinearMap.analyticAt _).comp
      (hG m hm z (Set.mem_univ _))

/-- On h0, the inverse map's physical field is actualPhiInv of the lp sequence. -/
theorem physInv_Tinv (z : ℤ → ℂ) (hz : z ∈ seqSobolev38 0) (h : actualTinv38 z ∈ seqSobolev38 0) :
    physInv38 (actualTinv38 z) h = actualPhiInv (seqToLp38 z hz) := by
  have e : actualTinv38 z = fourierSeq38 (actualPhiInv (seqToLp38 z hz)) := by
    unfold actualTinv38; rw [dif_pos hz]
  apply fourierSeq38_injective
  rw [fourierSeq38_physInv38, e]

end
end BirkhoffTopCore
end NlsGge.ThirdConsultation.PDE
