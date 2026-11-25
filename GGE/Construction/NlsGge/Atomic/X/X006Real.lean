import Mathlib
import NlsGge.Atomic.X.X006
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic

                                                                                                        
                                                                                                      
                                                                                                      
                                                                                                       
                                                                                      
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
