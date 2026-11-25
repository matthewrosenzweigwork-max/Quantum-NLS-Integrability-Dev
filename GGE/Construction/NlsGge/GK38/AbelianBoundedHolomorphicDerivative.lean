import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.MeanValue

/-! Uniform holomorphic bounds earn equicontinuity of actual derivatives.
This uses no compactness of an open Banach ball and no uniform-tail premise.
Actual period-map realization and the all-index invertibility tube are separate. -/
set_option autoImplicit false
open Set Metric
namespace NlsGge.GK38.P6HolomorphicBounds
noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

theorem norm_fderiv_le_of_ball_bound (f : E → F) (c : E) (R M : ℝ)
    (hR : 0 < R) (ha : AnalyticOnNhd ℂ f (ball c R))
    (hb : ∀ z ∈ ball c R, ‖f z‖ ≤ M) (x : E) (hx : x ∈ ball c (R/2)) :
    ‖fderiv ℂ f x‖ ≤ 4*M/R := by
  have hhalf : 0 < R/2 := half_pos hR
  have hsub : ball x (R/2) ⊆ ball c R := by
    intro z hz
    have ht := dist_triangle z x c
    have hz' := mem_ball.mp hz
    have hx' := mem_ball.mp hx
    exact mem_ball.mpr (by linarith)
  have hxR : x ∈ ball c R := hsub (mem_ball_self hhalf)
  have hd : DifferentiableOn ℂ f (ball x (R/2)) := by
    intro z hz
    exact (ha z (hsub hz)).differentiableAt.differentiableWithinAt
  have hm : MapsTo f (ball x (R/2)) (closedBall (f x) (2*M)) := by
    intro z hz
    apply mem_closedBall.mpr
    rw [dist_eq_norm]
    exact (norm_sub_le _ _).trans (by linarith [hb z (hsub hz),hb x hxR])
  have h := Complex.norm_fderiv_le_div_of_mapsTo_ball hd hm hhalf
  convert h using 1 <;> ring

theorem norm_sub_le_of_ball_bound (f : E → F) (c : E) (R M : ℝ)
    (hR : 0 < R) (ha : AnalyticOnNhd ℂ f (ball c R))
    (hb : ∀ z ∈ ball c R, ‖f z‖ ≤ M)
    (x y : E) (hx : x ∈ ball c (R/2)) (hy : y ∈ ball c (R/2)) :
    ‖f x-f y‖ ≤ (4*M/R)*‖x-y‖ := by
  apply Convex.norm_image_sub_le_of_norm_fderiv_le
    (𝕜 := ℂ) (s := ball c (R/2))
    (fun z hz => (ha z (ball_subset_ball (by linarith) hz)).differentiableAt)
    (fun z hz => norm_fderiv_le_of_ball_bound f c R M hR ha hb z hz)
    (convex_ball c (R/2)) hy hx

theorem norm_fderiv_sub_le_of_ball_bound (f : E → F) (c : E) (R M : ℝ)
    (hR : 0 < R) (ha : AnalyticOnNhd ℂ f (ball c R))
    (hb : ∀ z ∈ ball c R, ‖f z‖ ≤ M)
    (x y : E) (hx : x ∈ ball c (R/4)) (hy : y ∈ ball c (R/4)) :
    ‖fderiv ℂ f x-fderiv ℂ f y‖ ≤ (32*M/R^2)*‖x-y‖ := by
  have hha : AnalyticOnNhd ℂ (fderiv ℂ f) (ball c (R/2)) :=
    ha.fderiv.mono (ball_subset_ball (by linarith))
  have hh := norm_sub_le_of_ball_bound (fderiv ℂ f) c (R/2) (4*M/R)
    (half_pos hR) hha (fun z hz => norm_fderiv_le_of_ball_bound f c R M hR ha hb z hz)
    x y (by convert hx using 1 <;> ring) (by convert hy using 1 <;> ring)
  convert hh using 1 <;> field_simp <;> ring

end
end NlsGge.GK38.P6HolomorphicBounds
