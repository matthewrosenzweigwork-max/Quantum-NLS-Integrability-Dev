import NlsGge.GK38.TauGammaExteriorAnalytic
import NlsGge.GK38.TauGammaCriticalAnalytic

/-! Local joint analyticity yields both actual critical evaluations, with the scalar derivative checked. -/
set_option autoImplicit false
open Filter Topology Set Metric
namespace NlsGge.GK38
noncomputable section

theorem exterior_deriv_joint_analytic38 (V : Set PotPair) (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hV : IsOpen V) (hVW : V ⊆ gkW) (hf : ∀ φ ∈ V, IsolatingFamily38 φ C R) (n : ℤ) :
    AnalyticOnNhd ℂ (fun p : PotPair × ℂ => deriv (exteriorFactor38 p.1 n) p.2)
      (V ×ˢ ball (C n) (R n)) := by
  let S := V ×ˢ ball (C n) (R n)
  let F : PotPair × ℂ → ℂ := fun p => exteriorFactor38 p.1 n p.2
  let e : (PotPair × ℂ →L[ℂ] ℂ) →L[ℂ] ℂ := ContinuousLinearMap.apply ℂ ℂ (0, 1)
  have hS : IsOpen S := hV.prod isOpen_ball
  have hF := exterior_joint_analytic38 V C R hV hVW hf n
  have he (q : PotPair × ℂ) (hq : q ∈ S) : e (fderiv ℂ F q) = deriv (exteriorFactor38 q.1 n) q.2 := by
    have hd := (hF q hq).differentiableAt.hasFDerivAt
    have hi : HasDerivAt (fun z : ℂ => (q.1, z)) (0, 1) q.2 :=
      (hasDerivAt_const q.2 q.1).prodMk (hasDerivAt_id q.2)
    exact (hd.comp_hasDerivAt q.2 hi).deriv.symm
  intro p hp
  have h := (e.analyticAt (fderiv ℂ F p)).comp (hF p hp).fderiv
  apply h.congr
  filter_upwards [hS.mem_nhds hp] with q hq
  exact he q hq

theorem exterior_critical_analytic38 (n : ℤ) :
    AnalyticOnNhd ℂ (fun φ => exteriorFactor38 φ n (lamDot φ n)) gkW := by
  intro φ hφ
  obtain ⟨V, hV, hVW, hVo, _, C, R, hf⟩ := local_isolatingFamily φ hφ
  have hφV := mem_of_mem_nhds hV
  obtain ⟨c, N, hg, hs⟩ := hf φ hφV
  have hloc : (φ, lamDot φ n) ∈ V ×ˢ ball (C n) (R n) := ⟨hφV, (hs.1 n).2.2.2.1⟩
  have hQ := exterior_joint_analytic38 V C R hVo hVW hf n (φ, lamDot φ n) hloc
  exact AnalyticAt.comp (g := fun p : PotPair × ℂ => exteriorFactor38 p.1 n p.2)
    (f := fun ψ : PotPair => (ψ, lamDot ψ n)) hQ (analyticAt_id.prod (lamDot_analytic38 n φ hφ))

theorem exterior_deriv_critical_analytic38 (n : ℤ) :
    AnalyticOnNhd ℂ (fun φ => deriv (exteriorFactor38 φ n) (lamDot φ n)) gkW := by
  intro φ hφ
  obtain ⟨V, hV, hVW, hVo, _, C, R, hf⟩ := local_isolatingFamily φ hφ
  have hφV := mem_of_mem_nhds hV
  obtain ⟨c, N, hg, hs⟩ := hf φ hφV
  have hloc : (φ, lamDot φ n) ∈ V ×ˢ ball (C n) (R n) := ⟨hφV, (hs.1 n).2.2.2.1⟩
  have hQ := exterior_deriv_joint_analytic38 V C R hVo hVW hf n (φ, lamDot φ n) hloc
  exact AnalyticAt.comp (g := fun p : PotPair × ℂ => deriv (exteriorFactor38 p.1 n) p.2)
    (f := fun ψ : PotPair => (ψ, lamDot ψ n)) hQ (analyticAt_id.prod (lamDot_analytic38 n φ hφ))

end
end NlsGge.GK38
