import NlsGge.GK38.XiSqCenteredKernel
import NlsGge.GK38.XiSqExistence

set_option autoImplicit false
open Set Filter Topology Metric
namespace NlsGge.GK38
noncomputable section

/-- Genuine fixed-boundary analyticity supplies the centered local coordinate on the full V. -/
theorem a5CenteredLocalXi_analytic38 (V : Set PotPair) (hVo : IsOpen V) (hVW : V ⊆ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hf : ∀ φ ∈ V, IsolatingFamily38 φ C R)
    (φ₀ : PotPair) (hφ₀ : φ₀ ∈ V) (n : ℤ) :
    AnalyticOnNhd ℂ (a5CenteredLocalXi38 n (C n) (R n)) V := by
  have hjoint : AnalyticOnNhd ℂ
      (Function.uncurry (fun φ z => a5CenteredKernel38 n (φ, z)))
      (V ×ˢ sphere (C n) (R n)) := by
    intro p hp
    exact a5CenteredKernel_analytic38 n p
      ⟨hVW hp.1, fixed_sphere_subset p.1 C R (hf p.1 hp.1) n hp.2⟩
  have hi := Lib.parametricCircleAnalytic38 PotPair V (C n) (R n)
    (fun φ z => a5CenteredKernel38 n (φ, z)) hVo (isolating_radius_pos38 (hf φ₀ hφ₀) n) hjoint
  exact analyticOnNhd_const.mul hi.2

/-- Actual analytic cancellation identifies the coordinate EVEN at complex collapsed gaps. -/
theorem a5CenteredLocalXi_eq_candidate38 (n : ℤ) (g : PotPair → ℂ) (hg : XiSqSpec38 n g)
    (V : Set PotPair) (hVo : IsOpen V) (hVW : V ⊆ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hf : ∀ φ ∈ V, IsolatingFamily38 φ C R)
    (φ : PotPair) (hφ : φ ∈ V) : a5CenteredLocalXi38 n (C n) (R n) φ = g φ := by
  have hlocal := a5CenteredLocalXi_analytic38 V hVo hVW C R hf φ hφ n
  have hw : ∃ ψ ∈ gkW, gamma2 ψ n ≠ 0 := by
    refine ⟨realSlice (a5OpenWitness38 n), realSlice_mem_gkW _, ?_⟩
    rw [a5OpenWitness_gamma2_38]
    norm_num
  apply NlsGge.Analysis.AnalyticDivisionGluing.cancel_at_of_eventually_mul_eq
    (gamma2_analytic n) isPreconnected_gkW hw (hVW hφ)
    (hlocal φ hφ).continuousAt (hg.1 φ (hVW hφ)).continuousAt
  filter_upwards [hVo.mem_nhds hφ] with ψ hψ
  exact (a5CenteredLocalXi_identity38 ψ (hVW hψ) C R (hf ψ hψ) n).trans
    (xiSqCandidate_multiplied38 n g hg ψ (hVW hψ)).symm

end
end NlsGge.GK38
