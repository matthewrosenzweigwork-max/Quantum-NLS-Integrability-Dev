import NlsGge.GK38.AbelianActualCommonInteriorComplexLevels
import NlsGge.GK38.AbelianAnalyticLevelSelection

/-! Concrete common-neighborhood complex analytic level branches. Actual
compactness, inverse bounds, signed limits and quantitative root existence
are discharged by the concrete prerequisite; no analytic-selection oracle. -/
set_option autoImplicit false
open Set Metric
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem p6FullGap_common_complex_analytic_level_branches38 (u : PhysicalL2)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hfam : IsolatingFamily38 (realSlice u) C R) :
    ∃ r δ : ℝ, 0 < r ∧ 0 < δ ∧ ball (realSlice u) δ ⊆ gkW ∧
      ∀ b ∈ p6RealInclude38 '' p5FullRealGapCube38 u, ∀ n : ℤ,
        ∃ ψ : PotPair → Lib.L2Seq,
          ψ (realSlice u)=b ∧ AnalyticOnNhd ℂ ψ (ball (realSlice u) δ) ∧
          ∀ φ ∈ ball (realSlice u) δ,
            ψ φ ∈ closedBall b (r/2) ∧
            p6PaddedFn38 n (φ,ψ φ)=p6PaddedFn38 n (realSlice u,b) ∧
            ∀ y ∈ closedBall b r,
              p6PaddedFn38 n (φ,y)=p6PaddedFn38 n (realSlice u,b) → y=ψ φ := by
  classical
  obtain ⟨r,δ,B,hr,hδ,_hB,hW,hlevels⟩ :=
    p6FullGap_common_interior_complex_level_lifts38 u C R hfam
  let U : Set PotPair := ball (realSlice u) δ
  refine ⟨r,δ,hr,hδ,hW,?_⟩
  intro b hb n
  let ψ : PotPair → Lib.L2Seq := fun φ =>
    if hφ : φ ∈ U then Classical.choose (hlevels b hb φ hφ n) else b
  have hspec (φ : PotPair) (hφ : φ ∈ U) :
      ψ φ ∈ closedBall b (r/2) ∧
      p6PaddedFn38 n (φ,ψ φ)=p6PaddedFn38 n (realSlice u,b) ∧
      (∀ y ∈ closedBall b r,
        p6PaddedFn38 n (φ,y)=p6PaddedFn38 n (realSlice u,b) → y=ψ φ) ∧
      ∀ y ∈ closedBall b r, (p6PaddedJacobian38 n φ y).IsInvertible ∧
        ‖(p6PaddedJacobian38 n φ y).inverse‖ ≤ B := by
    simpa only [ψ,dite_eq_left hφ] using Classical.choose_spec (hlevels b hb φ hφ n)
  have hopen (φ : PotPair) (hφ : φ ∈ U) : ψ φ ∈ ball b r :=
    mem_ball.mpr ((mem_closedBall.mp (hspec φ hφ).1).trans_lt (half_lt_self hr))
  have hφ₀ : realSlice u ∈ U := mem_ball_self hδ
  have hψbase : ψ (realSlice u)=b :=
    ((hspec (realSlice u) hφ₀).2.2.1 b (mem_closedBall_self hr.le) rfl).symm
  have hψan : AnalyticOnNhd ℂ ψ U :=
    p6PaddedFn_interior_level_selection_analytic38 n b r U isOpen_ball hW
      (p6PaddedFn38 n (realSlice u,b)) ψ
      (fun φ hφ => ⟨hopen φ hφ,(hspec φ hφ).2.1⟩)
      (fun φ hφ y hy hyz => (hspec φ hφ).2.2.1 y (ball_subset_closedBall hy) hyz)
      (fun φ hφ => ((hspec φ hφ).2.2.2 (ψ φ)
        (ball_subset_closedBall (hopen φ hφ))).1)
  refine ⟨ψ,hψbase,hψan,?_⟩
  intro φ hφ
  exact ⟨(hspec φ hφ).1,(hspec φ hφ).2.1,(hspec φ hφ).2.2.1⟩

end
end NlsGge.GK38
