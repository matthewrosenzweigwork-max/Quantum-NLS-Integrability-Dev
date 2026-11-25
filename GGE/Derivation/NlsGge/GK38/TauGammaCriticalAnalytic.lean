import NlsGge.GK38.TauGammaCriticalMoments
import NlsGge.GK38.TauGammaSpectralDerivatives
import NlsGge.GK38.Lib.ParamCircleAnalytic

/-! Canonical critical-label analyticity is earned from its actual integrable singleton moment. -/
set_option autoImplicit false
open Filter Topology Set Metric
namespace NlsGge.GK38
noncomputable section

theorem critical_moment_boundary_analytic38 (V : Set PotPair) (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hf : ∀ φ ∈ V, IsolatingFamily38 φ C R) (n : ℤ) :
    AnalyticOnNhd ℂ (fun p : PotPair × ℂ => p.2 * deriv (deriv (discrim p.1)) p.2 /
      deriv (discrim p.1) p.2) (V ×ˢ sphere (C n) (R n)) := by
  intro p hp
  exact (analyticAt_snd.mul (analyticOnNhd_discrimSecondDeriv_joint38 p (mem_univ _))).div
    (analyticOnNhd_discrimDeriv_joint38 p (mem_univ _))
    (isolating_critical_boundary38 (hf p.1 hp.1) n p.2 hp.2)

theorem critical_fixedMoment_analytic38 (V : Set PotPair) (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hV : IsOpen V) (hf : ∀ φ ∈ V, IsolatingFamily38 φ C R)
    (φ₀ : PotPair) (hφ₀ : φ₀ ∈ V) (n : ℤ) :
    AnalyticOnNhd ℂ (fun φ => (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
      circleIntegral (fun z => z * deriv (deriv (discrim φ)) z / deriv (discrim φ) z)
        (C n) (R n)) V := by
  have h := Lib.parametricCircleAnalytic38 PotPair V (C n) (R n)
    (fun φ z => z * deriv (deriv (discrim φ)) z / deriv (discrim φ) z) hV
    (isolating_radius_pos38 (hf φ₀ hφ₀) n) (critical_moment_boundary_analytic38 V C R hf n)
  have hint := h.1
  exact analyticOnNhd_const.mul h.2

theorem lamDot_analytic38 (n : ℤ) : AnalyticOnNhd ℂ (fun φ => lamDot φ n) gkW := by
  intro φ hφ
  obtain ⟨V, hV, _, hVo, _, C, R, hf⟩ := local_isolatingFamily φ hφ
  have hφV := mem_of_mem_nhds hV
  have h := critical_fixedMoment_analytic38 V C R hVo hf φ hφV n
  apply (h φ hφV).congr
  filter_upwards [hV] with ψ hψ
  exact critical_fixedMoment38 ψ C R (hf ψ hψ) n

end
end NlsGge.GK38
