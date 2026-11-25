                                                                                                                                                                                                                                                         
import NlsGge.Hierarchy.ALSampling38

                                                                                                                                                                                                             
                                                                                                       
                                                                     

set_option autoImplicit false
open Set Filter Topology NlsGge.AblowitzLadik NlsGge.HierarchyRiccati.Core NlsGge.Pilot NlsGge.Analysis

namespace NlsGge.ThirdConsultation.AL
noncomputable section

theorem al057 (x : ℕ → SobolevHilbert 1) (u : SobolevHilbert 1)
    (hx : Tendsto x atTop (𝓝 u)) :
    Tendsto (fun N =>
      ‖physicalH1CanonicalContinuousRepresentativeCLM (x N - u)‖)
      atTop (𝓝 0) ∧
    (∃ M : ℝ, 0 ≤ M ∧ ∀ N : ℕ, ∀ t : ℝ, ‖alCanon38 (x N) t‖ ≤ M) ∧
    (∀ᶠ N : ℕ in atTop, ∀ j : ZMod (2 * N + 1),
      alh38 N * ‖alSample38 N (x N) j‖ < 1) := by
  refine ⟨?_, ?_, alDiskSample38 x u hx⟩
  · have hxn : Tendsto (fun N => x N - u) atTop (𝓝 0) := by
      have h := hx.sub_const u
      rwa [sub_self] at h
    have hc := ((physicalH1CanonicalContinuousRepresentativeCLM).continuous.tendsto
      (0 : SobolevHilbert 1)).comp hxn
    rw [map_zero] at hc
    have hn := hc.norm
    rw [norm_zero] at hn
    exact hn
  · obtain ⟨B, hB⟩ := hx.norm.bddAbove_range
    refine ⟨max B 0 * ‖reciprocalBracketL2‖, mul_nonneg (le_max_right _ _) (norm_nonneg _),
      fun N t => ?_⟩
    have hN : ‖x N‖ ≤ max B 0 := le_trans (hB ⟨N, rfl⟩) (le_max_left _ _)
    calc ‖alCanon38 (x N) t‖ ≤ ‖x N‖ * ‖reciprocalBracketL2‖ := alCanon_norm_le38 (x N) t
      _ ≤ max B 0 * ‖reciprocalBracketL2‖ := mul_le_mul_of_nonneg_right hN (norm_nonneg _)

end
end NlsGge.ThirdConsultation.AL
