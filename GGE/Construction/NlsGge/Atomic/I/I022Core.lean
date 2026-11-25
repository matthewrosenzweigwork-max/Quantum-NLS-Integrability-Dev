import Mathlib
import NlsGge.ThirdConsultation.I.FiniteGapLaws
import NlsGge.Atomic.I.I019
import NlsGge.Birkhoff.H03Diagonal38b
import NlsGge.Birkhoff.S04Moments38

                                                                                                                 
                                                                                  
                                                                                                  
                                                                                                                    
                                                                                                        
                                                                                                                          
                                                                                                                      
                                                           
                                                                                                                        
                                                                                                       
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology ContDiff
open NlsGge.Pilot NlsGge.Measure NlsGge.Weights
open NlsGge.SpectralFoundations
open NlsGge.Birkhoff NlsGge.Sobolev38 NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation.I

namespace NlsGge.ThirdConsultation.I022C

theorem physFS_eq (Bk : BirkhoffTop38) (m : ℕ) (z : ℤ → ℂ) :
    physFS38 m (Bk.cleanΦinv z) = ofCarrier38 (m : ℝ) (reflC38 (m : ℝ) (Bk.cleanTinvC m z)) := by
  unfold physFS38
  rw [Bk.physH38_cleanΦinv m z]

theorem tendsto_physFS (Bk : BirkhoffTop38) (hB : ∀ z : ℤ → ℂ, Bk.cleanΦinv z = physicalOfSequence z)
    (c : ℕ → ℝ) (z : ℤ → ℂ) (hz : z ∈ Omega038 c) (Λ : ℕ → Finset ℤ) (hΛ : IsExhaustion38 Λ) (m : ℕ) :
    Tendsto (fun N : ℕ => physFS38 m (physicalOfSequence (projFin38 (Λ N) z))) atTop
      (𝓝 (physFS38 m (physicalOfSequence z))) := by
  have h := ((continuous_physFS_comp38 m).tendsto _).comp (Bk.tendsto_cleanTinvC_proj38 m c hz hΛ)
  rw [← hB z, physFS_eq Bk m z]
  refine h.congr (fun N => ?_)
  simp only [Function.comp_apply]
  rw [← hB (projFin38 (Λ N) z), physFS_eq Bk m]

theorem i022_of (Bk : BirkhoffTop38) (hB : ∀ z : ℤ → ℂ, Bk.cleanΦinv z = physicalOfSequence z)
    (lower upper : ℝ) (c : BoundedCoefficients lower upper)
    (z : ℤ → ℂ) (hz : z ∈ goodGaussianSet c.val) :
    (∀ m : ℕ, SobolevSquareSummable (m : ℝ) (physicalFourier (physicalOfSequence z))) ∧
    ∀ Λ : ℕ → Finset ℤ, IsExhaustion38 Λ →
      (∀ N m : ℕ, SobolevSquareSummable (m : ℝ)
        (physicalFourier (physicalOfSequence (projFin38 (Λ N) z)))) ∧
      (∀ m : ℕ, Tendsto
        (fun N : ℕ => physFS38 m (physicalOfSequence (projFin38 (Λ N) z))) atTop
        (𝓝 (physFS38 m (physicalOfSequence z)))) ∧
      ∃ B : ℝ, 0 ≤ B ∧ ‖physFS38 1 (physicalOfSequence z)‖ ≤ B ∧
        ∀ N : ℕ, ‖physFS38 1 (physicalOfSequence (projFin38 (Λ N) z))‖ ≤ B := by
  have hz' : z ∈ Omega038 c.val := hz
  refine ⟨fun m => ?_, fun Λ hΛ => ⟨fun N m => ?_, fun m => tendsto_physFS Bk hB c.val z hz' Λ hΛ m, ?_⟩⟩
  · rw [← hB z]
    exact Bk.sobolev_cleanΦinv38 m z (BirkhoffTop38.mem_seqSobolev38_of_Omega038 c.val hz' m)
  · rw [← hB]
    exact Bk.sobolev_cleanΦinv38 m _
      (finiteSupport_mem_seqSobolev38 _ _ (finite_support_projFin38 (Λ N) z))
  · have ht := (tendsto_physFS Bk hB c.val z hz' Λ hΛ 1).norm
    obtain ⟨M, hM⟩ := ht.bddAbove_range
    refine ⟨max M ‖physFS38 1 (physicalOfSequence z)‖,
      (norm_nonneg _).trans (le_max_right _ _), le_max_right _ _, fun N => ?_⟩
    exact (hM ⟨N, rfl⟩).trans (le_max_left _ _)

end NlsGge.ThirdConsultation.I022C
