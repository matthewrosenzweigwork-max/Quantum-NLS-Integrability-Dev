import NlsGge.GK38.ActionRadialGeometry

/-! Actual radial contour equality uses the traced annulus and earns integrability. -/
set_option autoImplicit false
open Set Metric Filter Topology MeasureTheory NlsGge.GK38
namespace NlsGge.GK38.ActionRadial
noncomputable section

theorem radial_contour_realization (φ : PotPair) (hφ : φ ∈ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hf : IsolatingFamily38 φ C R)
    (n : ℤ) (r : ℝ) (hr : 0 < r) (hrR : r ≤ R n)
    (hown : segment ℝ (lamMinus φ n) (lamPlus φ n) ⊆ ball (C n) r)
    (f : ℂ → ℂ) (ha : AnalyticOnNhd ℂ f (actionCutDomain38 φ)) :
    CircleIntegrable f (C n) (R n) ∧ CircleIntegrable f (C n) r ∧
      circleIntegral f (C n) (R n) = circleIntegral f (C n) r := by
  apply NlsGge.Analysis.circleIntegral_eq_of_affine_circle_homotopy
    (isOpen_actionCutDomain38 φ hφ) ha (isolating_radius_pos38 hf n) hr
  intro t ht
  have hc : ((1 - t) : ℝ) • C n + t • C n = C n := by module
  rw [hc]
  apply radial_sphere_subset φ C R hf n r ((1 - t) * R n + t * r) _ _ hown
  · nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hrR)]
  · nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr hrR)]

theorem discrim_quotient_analytic (φ : PotPair) (hφ : φ ∈ gkW) :
    AnalyticOnNhd ℂ (fun z => deriv (discrim φ) z / canonRoot38 φ z)
      (actionCutDomain38 φ) := by
  intro z hz
  have hn := (analyticOnNhd_discrimDeriv_joint38 (φ, z) (mem_univ _)).comp
    ((analyticAt_const (v := φ)).prod analyticAt_id)
  have hd := (canonRoot_analytic38 (φ, z) ⟨hφ, hz⟩).comp
    ((analyticAt_const (v := φ)).prod analyticAt_id)
  exact hn.div hd (canonRoot_ne_zero38 φ hφ z hz)

theorem radial_unweighted_realization (φ : PotPair) (hφ : φ ∈ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hf : IsolatingFamily38 φ C R)
    (n : ℤ) (r : ℝ) (hr : 0 < r) (hrR : r ≤ R n)
    (hown : segment ℝ (lamMinus φ n) (lamPlus φ n) ⊆ ball (C n) r) :
    CircleIntegrable (fun z => deriv (discrim φ) z / canonRoot38 φ z) (C n) (R n) ∧
    CircleIntegrable (fun z => deriv (discrim φ) z / canonRoot38 φ z) (C n) r ∧
      circleIntegral (fun z => deriv (discrim φ) z / canonRoot38 φ z) (C n) (R n) =
        circleIntegral (fun z => deriv (discrim φ) z / canonRoot38 φ z) (C n) r :=
  radial_contour_realization φ hφ C R hf n r hr hrR hown _
    (discrim_quotient_analytic φ hφ)

theorem radial_action_realization (φ : PotPair) (hφ : φ ∈ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hf : IsolatingFamily38 φ C R)
    (n : ℤ) (r : ℝ) (hr : 0 < r) (hrR : r ≤ R n)
    (hown : segment ℝ (lamMinus φ n) (lamPlus φ n) ⊆ ball (C n) r) :
    CircleIntegrable (actionIntegrand38 φ) (C n) (R n) ∧
    CircleIntegrable (actionIntegrand38 φ) (C n) r ∧
      gkActionC38 φ n = contourAction38 φ (C n) r := by
  have he := radial_contour_realization φ hφ C R hf n r hr hrR hown _
    (actionIntegrand_analytic38 φ hφ)
  refine ⟨he.1, he.2.1, ?_⟩
  have hold := action_contour_independence38 φ hφ (discC φ) C (discR φ) R
    (isolating_family38 φ hφ) hf n
  change contourAction38 φ (discC φ n) (discR φ n) = _
  exact hold.trans (congrArg (fun a : ℂ => (1 / (Real.pi : ℂ)) * a) he.2.2)

end
end NlsGge.GK38.ActionRadial
