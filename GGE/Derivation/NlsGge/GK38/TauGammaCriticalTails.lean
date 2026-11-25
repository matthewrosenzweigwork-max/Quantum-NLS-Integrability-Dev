import NlsGge.GK38.TauGammaCriticalAnalytic
import NlsGge.GK38.TauGammaL2Realization

/-! Critical uniform tails follow a genuine analytic Hilbert-valued realization. -/
set_option autoImplicit false
open Filter Topology Set Metric
namespace NlsGge.GK38
noncomputable section

theorem critical_l2_realization38 :
    ∃ A : PotPair → Lib.L2Z,
      (∀ φ ∈ gkW, ∀ n : ℤ, A φ n = lamDot φ n - (n : ℂ) * (Real.pi : ℂ)) ∧
      AnalyticOnNhd ℂ A gkW := by
  apply local_l2_analytic_realization38 gkW
    (fun φ n => lamDot φ n - (n : ℂ) * (Real.pi : ℂ)) isOpen_gkW
  · intro n
    exact (lamDot_analytic38 n).sub analyticOnNhd_const
  · intro φ _
    obtain ⟨U, hU, C, _, h⟩ := critical_l2 φ
    exact ⟨U, hU, C, h⟩

theorem critical_uniform_tail38 (φ₀ : PotPair) (hφ₀ : φ₀ ∈ gkW) (ε : ℝ) (hε : 0 < ε) :
    ∃ V : Set PotPair, V ∈ 𝓝 φ₀ ∧ V ⊆ gkW ∧ ∃ N : ℕ,
      ∀ φ ∈ V, ∀ n : ℤ, (N : ℤ) < |n| →
        ‖lamDot φ n - (n : ℂ) * (Real.pi : ℂ)‖ < ε := by
  obtain ⟨A, he, ha⟩ := critical_l2_realization38
  obtain ⟨V, hV, N, ht⟩ := l2_continuous_local_tails38 A φ₀ (ha φ₀ hφ₀).continuousAt ε hε
  refine ⟨V ∩ gkW, inter_mem hV (isOpen_gkW.mem_nhds hφ₀), inter_subset_right, N, ?_⟩
  intro φ hφ n hn
  rw [← he φ hφ.2 n]
  exact ht φ hφ.1 n hn

end
end NlsGge.GK38
