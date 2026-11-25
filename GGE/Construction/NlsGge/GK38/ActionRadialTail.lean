import NlsGge.GK38.ActionRadialIntegrals

/-! Fixed tail circles: retain the pi/4 family and shrink its traced contour to pi/8. -/
set_option autoImplicit false
open Set Metric Filter Topology MeasureTheory NlsGge.GK38
namespace NlsGge.GK38.ActionRadial
noncomputable section

theorem fixed_tail_contour_realization (φ : PotPair) (hφ : φ ∈ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hf : IsolatingFamily38 φ C R) (n : ℤ)
    (hC : C n = (n : ℂ) * (Real.pi : ℂ)) (hR : R n = Real.pi / 4)
    (hown : segment ℝ (lamMinus φ n) (lamPlus φ n) ⊆
      ball ((n : ℂ) * (Real.pi : ℂ)) (Real.pi / 16))
    (f : ℂ → ℂ) (ha : AnalyticOnNhd ℂ f (actionCutDomain38 φ)) :
    CircleIntegrable f ((n : ℂ) * (Real.pi : ℂ)) (Real.pi / 4) ∧
    CircleIntegrable f ((n : ℂ) * (Real.pi : ℂ)) (Real.pi / 8) ∧
      circleIntegral f ((n : ℂ) * (Real.pi : ℂ)) (Real.pi / 4) =
        circleIntegral f ((n : ℂ) * (Real.pi : ℂ)) (Real.pi / 8) := by
  have hr : 0 < Real.pi / 8 := div_pos Real.pi_pos (by norm_num)
  have hrR : Real.pi / 8 ≤ R n := by rw [hR]; linarith [Real.pi_pos]
  have hown8 : segment ℝ (lamMinus φ n) (lamPlus φ n) ⊆ ball (C n) (Real.pi / 8) := by
    rw [hC]
    exact hown.trans (ball_subset_ball (by linarith [Real.pi_pos]))
  simpa only [hC, hR] using
    radial_contour_realization φ hφ C R hf n (Real.pi / 8) hr hrR hown8 f ha

end
end NlsGge.GK38.ActionRadial
