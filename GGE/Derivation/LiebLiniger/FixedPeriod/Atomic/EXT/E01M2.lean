import LiebLiniger.FixedPeriod.Atomic.EXT.FlowRotationC6
import LiebLiniger.FixedPeriod.Atomic.EXT.R2b2
import NlsGge.Birkhoff.S04FiniteGapInvariance38
import NlsGge.NLS38.FlowMeasure38

/-! # Actual finite-gap physical Liouville invariance

The action-dependent rotation of the actual NLS flow preserves ordinary
planar product volume. Transport through the actual finite-gap chart and the
form-derived physical normalization gives the restricted symplectic-volume
invariance asserted in `paper/v2.tex`, line 445.
-/

set_option autoImplicit false
noncomputable section
namespace LiebLiniger.FixedPeriod.EXT

open MeasureTheory NlsGge.Birkhoff NlsGge.NLS38
open NlsGge.ThirdConsultation.PDE

/-- For every finite set of Birkhoff indices and every real time, the actual
NLS flow preserves the induced physical Liouville measure on the whole actual
finite-gap manifold. Empty planes, zero modes and zero coordinates are included. -/
theorem actual_finiteGap_physical_liouville_invariant38 :
    ∀ (Λ : Finset ℤ) (t : ℝ),
      MeasureTheory.Measure.map (NlsGge.NLS38.nlsFlowL2 t)
        (LiebLiniger.FixedPeriod.EXT.inducedFiniteGapPhysicalLiouville38 Λ) =
          LiebLiniger.FixedPeriod.EXT.inducedFiniteGapPhysicalLiouville38 Λ := by
  intro Λ t
  obtain ⟨Ω, hΩm, hΩ⟩ := actualBirkhoffNLSFlowInput38.rotation
  -- Establish measurability before using any pushforward composition.
  have hκ : Measurable (kappaΛ38 Ω Λ t) := measurable_kappaΛ38 Ω hΩm Λ t
  have hT : Measurable (twist (kappaΛ38 Ω Λ t)) := measurable_twist _ hκ
  have hfield : Measurable (actualBirkhoffTop38.finiteGapField38 Λ) :=
    actualBirkhoffTop38.measurable_finiteGapField38 Λ
  have hflow : Measurable (nlsFlowL2 t) := measurable_nlsFlowL2 t
  -- The existing torus-averaging theorem applies to the complete finite plane.
  have hplane : (NlsGge.Measure.finiteComplexVolume Λ).map
      (twist (kappaΛ38 Ω Λ t)) = NlsGge.Measure.finiteComplexVolume Λ :=
    (measurePreserving_twist _ hκ (kappaΛ38_rotate Ω Λ t)).map_eq
  -- Actual conjugacy is pointwise, so no exceptional representatives are needed.
  have hcomp : nlsFlowL2 t ∘ actualBirkhoffTop38.finiteGapField38 Λ =
      actualBirkhoffTop38.finiteGapField38 Λ ∘ twist (kappaΛ38 Ω Λ t) := by
    funext w
    exact finiteGapField_rotation_of actualBirkhoffTop38
      nlsFlowL2 Ω hΩ Λ w t
  simp only [actual_finiteGap_physical_liouville_eq]
  rw [Measure.map_smul _ hflow.aemeasurable, Measure.map_map hflow hfield,
    hcomp, ← Measure.map_map hfield hT, hplane]

end LiebLiniger.FixedPeriod.EXT
