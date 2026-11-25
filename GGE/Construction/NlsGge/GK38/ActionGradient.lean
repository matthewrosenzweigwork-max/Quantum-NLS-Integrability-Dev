import NlsGge.GK38.ActionGradientFixedCircle

set_option autoImplicit false
open Set Metric Filter Topology MeasureTheory
open NlsGge.GK38 NlsGge.Pilot
namespace NlsGge.GK38.ActionGradient
noncomputable section

theorem selected_family_persists (φ : PotPair) (hφ : φ ∈ gkW) :
    ∃ V : Set PotPair, IsOpen V ∧ φ ∈ V ∧ V ⊆ gkW ∧
      ∀ ψ ∈ V, IsolatingFamily38 ψ (discC φ) (discR φ) := by
  obtain ⟨ρ, hρ, κ, N, hg, hs⟩ := fixed_family_persistence38 φ (discC φ) (discR φ)
    (isolating_family38 φ hφ)
  refine ⟨ball φ ρ ∩ gkW, isOpen_ball.inter isOpen_gkW,
    ⟨mem_ball_self hρ, hφ⟩, inter_subset_right, ?_⟩
  intro ψ hψ
  exact ⟨κ, N, hg, hs ψ hψ.1⟩

theorem action_hasFDeriv (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) :
    HasFDerivAt (fun ψ : PotPair => gkActionC38 ψ n) (actionGradientCLM38 φ n) φ := by
  obtain ⟨V, hVo, hφV, hVW, hf⟩ := selected_family_persists φ hφ
  have hd := fixed_contour_hasFDeriv V hVo hVW (discC φ) (discR φ) hf φ hφV n
  have he : (fun ψ : PotPair => gkActionC38 ψ n) =ᶠ[𝓝 φ]
      (fun ψ : PotPair => contourAction38 ψ (discC φ n) (discR φ n)) := by
    filter_upwards [hVo.mem_nhds hφV] with ψ hψ
    exact local_fixed_agreement38 V hVW (discC φ) (discR φ) hf ψ hψ n
  exact hd.congr_of_eventuallyEq he

theorem action_fderiv_apply (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) (h : PotPair) :
    fderiv ℂ (fun ψ : PotPair => gkActionC38 ψ n) φ h = -(1 / (Real.pi : ℂ)) *
      circleIntegral (fun z => gradDiscrimCLM φ z h / canonRoot38 φ z)
        (discC φ n) (discR φ n) := by
  rw [(action_hasFDeriv φ hφ n).fderiv]
  exact actionGradientCLM_apply φ hφ n h

end
end NlsGge.GK38.ActionGradient
