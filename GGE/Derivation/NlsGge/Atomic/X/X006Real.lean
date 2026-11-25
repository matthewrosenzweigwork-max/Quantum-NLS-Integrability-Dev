import Mathlib
import NlsGge.Atomic.X.X006
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic

/- X006REAL PRODUCTION01 (proof development, AUTHOR; not self-reviewed). Target NlsGge/Atomic/X/X006Real.lean,
   namespace NlsGge.GKDefinitionDesign. Supporting result M1 for KSN-001 (proof development/KSN001_STOP.md),
   head verbatim from that STOP file. Route (proof development/M1_DECISION.md, option A; owner decision 17):
   the third conjunct of the strengthened X-006 existential gives a ball around a real potential inside
   sourceBetaW = sourceFamily.V containing φ; a ball is convex, hence preconnected. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem sourceBetaW_realConnected :
  ∀ φ ∈ sourceBetaW, ∃ S : Set PotPair,
    IsOpen S ∧ IsPreconnected S ∧ S ⊆ sourceBetaW ∧ φ ∈ S ∧ ∃ u : PhysicalL2, realSlice u ∈ S := by
  intro φ hφ
  obtain ⟨u, r, hr, hφr, hsub⟩ :=
    (Classical.choose_spec
      NlsGge.Atomic.ExistingPhysicalFamily.physicalLocalFamily_with_retained_bounds).2.2 φ hφ
  exact ⟨Metric.ball (realSlice u) r, Metric.isOpen_ball, (convex_ball _ _).isPreconnected,
    hsub, hφr, u, Metric.mem_ball_self hr⟩

end
end NlsGge.GKDefinitionDesign
