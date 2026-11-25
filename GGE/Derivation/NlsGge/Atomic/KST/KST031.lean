import Mathlib
import NlsGge.ThirdConsultation.KST.KST031Host
import NlsGge.ThirdConsultation.KST.KST031Support

/- KST-031 PRODUCTION01 (proof development, AUTHOR; not self-reviewed).  Target NlsGge/Atomic/KST/KST031.lean,
   namespace NlsGge.ThirdConsultation.KST.  Head VERBATIM from Pro rounds 7-8, section 25
   (gpt6pro_followup10/handoff/definitions_followup_20261030/PRO_DEFINITION_RESPONSE_FP80_07_08.md:1488-1501,
   BINDING_INDEX_FP80_07_08.json packet KST-031): last quantifier widened to every v with 1 <= v k.
   No later Pro round (9-12) touches KST-031.  Route: Pro section 25 "Dependency ruling" (compact L2 closure of the
   weighted ball + finite cover by the local KST-029 / KST-011 neighbourhoods; max of the cutoffs) and the direct
   ball-inclusion transfer for the product weight.  Supports: KST031Host (design defs), KST031Support (compactness, cover). -/
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
