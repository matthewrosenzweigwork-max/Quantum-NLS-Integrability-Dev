import NlsGge.GK38.AbelianPaddedJacobianEquicontinuity
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn

/-! Actual common linear approximation near any full complex base input.
The radius precedes every signed index, nearby seed and varying potential.
This is a local prerequisite; compact globalization and residuals are separate. -/
set_option autoImplicit false
open Set Metric
open scoped NNReal
namespace NlsGge.GK38
noncomputable section

theorem p6PaddedFn_local_common_linear_approximation38
    (φ₀ : PotPair) (hφ₀ : φ₀ ∈ gkW) (s₀ : Lib.L2Seq)
    (c : ℝ≥0) (hc : 0 < c) :
    ∃ ρ : ℝ, 0 < ρ ∧ ball φ₀ ρ ⊆ gkW ∧
      ∀ b ∈ ball s₀ ρ, ∀ φ ∈ ball φ₀ ρ, ∀ n : ℤ,
        ApproximatesLinearOn (fun x : Lib.L2Seq => p6PaddedFn38 n (φ,x))
          (p6PaddedJacobian38 n φ₀ b) (closedBall b ρ) c := by
  obtain ⟨R,L,hR,hL,hdom,hLip⟩ :=
    p6PaddedJacobian_local_uniform_lipschitz38 φ₀ hφ₀ s₀
  let ρ : ℝ := min (R/4) ((c : ℝ)/(4*(L+1)))
  have hcR : 0 < (c : ℝ) := hc
  have hden : 0 < 4*(L+1) := by positivity
  have hρ : 0 < ρ := lt_min (by positivity) (div_pos hcR hden)
  have hρR : ρ ≤ R/4 := min_le_left _ _
  have hρc : ρ ≤ (c : ℝ)/(4*(L+1)) := min_le_right _ _
  have hmul : ρ*(4*(L+1)) ≤ (c : ℝ) := (le_div_iff₀ hden).mp hρc
  have hLc : L*ρ ≤ (c : ℝ) := by nlinarith [mul_nonneg hL hρ.le]
  have hsmall : 2*ρ < R := by linarith
  have hpot : ball φ₀ ρ ⊆ gkW := by
    intro φ hφ
    have hp : (φ,s₀) ∈ ball (φ₀,s₀) R := by
      rw [mem_ball,Prod.dist_eq,dist_self]
      exact max_lt (lt_of_lt_of_le (mem_ball.mp hφ) (by linarith)) hR
    exact (hdom hp).1
  refine ⟨ρ,hρ,hpot,?_⟩
  intro b hb φ hφ n x hx y hy
  have hbase : (φ₀,b) ∈ ball (φ₀,s₀) R := by
    rw [mem_ball,Prod.dist_eq,dist_self]
    exact max_lt hR ((mem_ball.mp hb).trans (by linarith))
  have hpoint (z : Lib.L2Seq) (hz : z ∈ closedBall b ρ) :
      (φ,z) ∈ ball (φ₀,s₀) R := by
    rw [mem_ball,Prod.dist_eq]
    refine max_lt ((mem_ball.mp hφ).trans (by linarith)) ?_
    have ht := dist_triangle z b s₀
    have hzb := mem_closedBall.mp hz
    have hbs := mem_ball.mp hb
    linarith
  have hbound (z : Lib.L2Seq) (hz : z ∈ closedBall b ρ) :
      ‖p6PaddedJacobian38 n φ z-p6PaddedJacobian38 n φ₀ b‖ ≤ (c : ℝ) := by
    have hd : ‖(φ,z)-(φ₀,b)‖ ≤ ρ := by
      rw [← dist_eq_norm,Prod.dist_eq]
      exact max_le (mem_ball.mp hφ).le (mem_closedBall.mp hz)
    exact (hLip n (φ,z) (hpoint z hz) (φ₀,b) hbase).trans
      ((mul_le_mul_of_nonneg_left hd hL).trans hLc)
  exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun z hz => (p6PaddedFn_hasFDerivAt38 n φ (hpot hφ) z).hasFDerivWithinAt)
    hbound (convex_closedBall b ρ) hy hx

end
end NlsGge.GK38
