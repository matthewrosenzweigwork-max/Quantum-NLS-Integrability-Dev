import NlsGge.GK38.TauGamma
import NlsGge.Analysis.AnalyticTsum38

/-! Uncompiled finite-trace prerequisite. Constants precede ALL finite subsets.
The local absolute mass is an existing actual spectral theorem; continuity of
its infinite trace is NOT assumed here. -/
set_option autoImplicit false
open Set Metric Filter Topology
namespace NlsGge.GK38
noncomputable section

theorem p5Gamma_finite_trace_bound38 (φ : PotPair) (S : Finset ℤ)
    (hs : Summable (fun m : ℤ => ‖gamma2 φ m‖)) :
    ‖∑ m ∈ S, gamma2 φ m‖ ≤ ∑' m : ℤ, ‖gamma2 φ m‖ := by
  exact (norm_sum_le _ _).trans (hs.sum_le_tsum S (fun _ _ => norm_nonneg _))

theorem p5Gamma_finite_trace_local_cauchy38 (φ₀ : PotPair) (hφ₀ : φ₀ ∈ gkW) :
    ∃ r B : ℝ, 0 < r ∧ 0 ≤ B ∧ closedBall φ₀ (2*r) ⊆ gkW ∧
      (∀ φ ∈ closedBall φ₀ (2*r), Summable (fun m : ℤ => ‖gamma2 φ m‖)) ∧
      (∀ S : Finset ℤ, ∀ φ ∈ closedBall φ₀ r,
        ‖fderiv ℂ (fun ψ : PotPair => ∑ m ∈ S, gamma2 ψ m) φ‖ ≤ B/r) ∧
      (∀ S : Finset ℤ, ∀ φ ∈ closedBall φ₀ r, ∀ ψ ∈ closedBall φ₀ r,
        ‖(∑ m ∈ S, gamma2 ψ m)-(∑ m ∈ S, gamma2 φ m)‖ ≤ (B/r)*‖ψ-φ‖) := by
  obtain ⟨V,hV,hVW,B,hB,h⟩ := tauGamma_common_value_bound38 discC discR
    isolating_selectors_admissible38 φ₀ hφ₀
  obtain ⟨ε,hε,hεV⟩ := Metric.mem_nhds_iff.mp hV
  let r : ℝ := ε/4
  have hr : 0 < r := by dsimp [r]; positivity
  have hVball : closedBall φ₀ (2*r) ⊆ V := by
    intro φ hφ
    apply hεV
    rw [mem_ball]
    exact (mem_closedBall.mp hφ).trans_lt (by dsimp [r]; linarith)
  have hW : closedBall φ₀ (2*r) ⊆ gkW := hVball.trans hVW
  have ha (S : Finset ℤ) : AnalyticOnNhd ℂ
      (fun φ : PotPair => ∑ m ∈ S, gamma2 φ m) (closedBall φ₀ (2*r)) := by
    intro φ hφ
    exact S.analyticAt_fun_sum (fun m _ => gamma2_analytic m φ (hW hφ))
  have hb (S : Finset ℤ) (φ : PotPair) (hφ : φ ∈ closedBall φ₀ (2*r)) :
      ‖∑ m ∈ S, gamma2 φ m‖ ≤ B :=
    (p5Gamma_finite_trace_bound38 φ S (h φ (hVball hφ)).2.2.1).trans
      (h φ (hVball hφ)).2.2.2.2.2
  have hd (S : Finset ℤ) (φ : PotPair) (hφ : φ ∈ closedBall φ₀ r) :
      ‖fderiv ℂ (fun ψ : PotPair => ∑ m ∈ S, gamma2 ψ m) φ‖ ≤ B/r :=
    NlsGge.AnalyticTsum38.norm_fderiv_le_of_closedBall38 (ha S) (hb S)
      hφ hr (by ring_nf; exact le_refl _)
  refine ⟨r,B,hr,hB,hW,(fun φ hφ => (h φ (hVball hφ)).2.2.1),hd,?_⟩
  intro S φ hφ ψ hψ
  exact Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun x hx => (ha S x (closedBall_subset_closedBall (by linarith) hx)).differentiableAt)
    (hd S) (convex_closedBall φ₀ r) hφ hψ

end
end NlsGge.GK38
