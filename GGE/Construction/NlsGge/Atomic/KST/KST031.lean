import Mathlib
import NlsGge.ThirdConsultation.KST.KST031Host
import NlsGge.ThirdConsultation.KST.KST031Support

                                                                                                        
                                                                                         
                                                                                                             
                                                                                                   
                                                                                                                   
                                                                                                                 
                                                                                                                              
set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped ENNReal

namespace NlsGge.ThirdConsultation.KST

attribute [local instance] Classical.propDecidable

theorem kst031 (w : ℤ → ℝ) (M : ℝ) (hM : 1 ≤ M)
    (hw : UnboundedWeight w) :
    (∃ N₄ : ℕ, uniformReducedBounds w M N₄) ∧
    uniformReducedBounds w M (diagonalThreshold w M) ∧
    ∀ v : ℤ → ℝ, (∀ k : ℤ, 1 ≤ v k) →
      uniformReducedBounds (productWeight w v) M
        (diagonalThreshold w M) := by
  have h1 : ∃ N₄ : ℕ, uniformReducedBounds w M N₄ :=
    KST031S.exists_uniformReducedBounds w hw M
  have h2 : uniformReducedBounds w M (diagonalThreshold w M) := by
    unfold diagonalThreshold
    rw [dif_pos h1]
    exact Nat.find_spec h1
  refine ⟨h1, h2, fun v hv => ?_⟩
  exact KST031S.uniformReducedBounds_of_ball_subset w (productWeight w v) M _
    (KST031S.ball_productWeight_subset w v hw.1.1 hv _) h2

end NlsGge.ThirdConsultation.KST
end
