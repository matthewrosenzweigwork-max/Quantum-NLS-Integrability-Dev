import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.Positivity

/-!
Differentiation of a Cauchy transform with a density given directly in
the circle parameter. No extension of the density to the complex plane
and no periodicity assumption are used.

The dominated differentiation argument is adapted from
`Complex.hasDerivAt_circleIntegral_sub_zpow_smul` in mathlib commit
`d13f23b723b8a846827a245b89c10fc7d3f11612`.
The mathlib source is Copyright (c) 2021 Yury Kudryashov and is released
under the Apache 2.0 license.
-/

set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory intervalIntegral

namespace NlsGge.GK38
noncomputable section

/-- A continuous circle-parameter density has the expected Cauchy
transform derivative at every point away from the circle. -/
theorem rawBetaCircleParameterCauchyHasDerivAt38
    (B : ℝ → ℂ) (hB : Continuous B) (c : ℂ) (r : ℝ)
    (w : ℂ) (hw : w ∉ sphere c |r|) :
    HasDerivAt
      (fun z : ℂ => ∫ θ in 0..2 * Real.pi,
        B θ * deriv (circleMap c r) θ / (circleMap c r θ - z))
      (∫ θ in 0..2 * Real.pi,
        B θ * deriv (circleMap c r) θ / (circleMap c r θ - w) ^ 2) w := by
  obtain ⟨d, hd, hdist⟩ := exists_ball_forall_le_norm_circleMap_sub hw
  let G : ℝ → ℂ := fun θ => B θ * deriv (circleMap c r) θ
  have hdc : Continuous (fun θ : ℝ => deriv (circleMap c r) θ) := by
    simpa only [deriv_circleMap] using
      (continuous_circleMap 0 r).mul_const Complex.I
  have hG : Continuous G := hB.mul hdc
  have hne (x : ℂ) (hx : x ∈ ball w d) (θ : ℝ) :
      circleMap c r θ - x ≠ 0 :=
    norm_pos_iff.mp (hd.trans_le (hdist x hx θ))
  have hFcont (x : ℂ) (hx : x ∈ ball w d) :
      Continuous (fun θ : ℝ => G θ / (circleMap c r θ - x)) :=
    hG.div ((continuous_circleMap c r).sub continuous_const) (hne x hx)
  have hFprimecont (x : ℂ) (hx : x ∈ ball w d) :
      Continuous (fun θ : ℝ => G θ / (circleMap c r θ - x) ^ 2) :=
    hG.div (((continuous_circleMap c r).sub continuous_const).pow 2)
      (fun θ => pow_ne_zero 2 (hne x hx θ))
  change HasDerivAt
    (fun z : ℂ => ∫ θ in 0..2 * Real.pi, G θ / (circleMap c r θ - z))
    (∫ θ in 0..2 * Real.pi, G θ / (circleMap c r θ - w) ^ 2) w
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z θ => G θ / (circleMap c r θ - z))
    (F' := fun z θ => G θ / (circleMap c r θ - z) ^ 2)
    (bound := fun θ => (d ^ 2)⁻¹ * ‖G θ‖)
    (ball_mem_nhds w hd) ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [ball_mem_nhds w hd] with x hx
    exact (hFcont x hx).aestronglyMeasurable
  · exact (hFcont w (mem_ball_self hd)).intervalIntegrable _ _
  · exact (hFprimecont w (mem_ball_self hd)).aestronglyMeasurable
  · filter_upwards with θ _ x hx
    rw [norm_div, norm_pow, div_eq_inv_mul]
    have hsq : d ^ 2 ≤ ‖circleMap c r θ - x‖ ^ 2 := by
      simpa only [pow_two] using
        mul_le_mul (hdist x hx θ) (hdist x hx θ) hd.le
          (norm_nonneg (circleMap c r θ - x))
    exact mul_le_mul_of_nonneg_right
      (inv_anti₀ (by positivity : 0 < d ^ 2) hsq) (norm_nonneg _)
  · exact (hG.norm.intervalIntegrable _ _).const_mul _
  · filter_upwards with θ _ x hx
    have hden : HasDerivAt (fun z : ℂ => circleMap c r θ - z) (-1) x := by
      simpa using! (hasDerivAt_id' x).const_sub (circleMap c r θ)
    simpa using! (hasDerivAt_const x (G θ)).fun_div hden (hne x hx θ)

/-- The parameter Cauchy transform is analytic in the filled open disc. -/
theorem rawBetaCircleParameterCauchyAnalytic38
    (B : ℝ → ℂ) (hB : Continuous B) (c : ℂ) (r : ℝ) :
    AnalyticOnNhd ℂ
      (fun z : ℂ => ∫ θ in 0..2 * Real.pi,
        B θ * deriv (circleMap c r) θ / (circleMap c r θ - z))
      (ball c r) := by
  have hd : DifferentiableOn ℂ
      (fun z : ℂ => ∫ θ in 0..2 * Real.pi,
        B θ * deriv (circleMap c r) θ / (circleMap c r θ - z))
      (ball c r) := by
    intro w hw
    have hr : 0 < r := lt_of_le_of_lt dist_nonneg (mem_ball.mp hw)
    have hwsphere : w ∉ sphere c |r| := by
      intro hs
      have hdist : dist w c = r := by
        simpa only [abs_of_pos hr] using mem_sphere.mp hs
      exact (ne_of_lt (mem_ball.mp hw)) hdist
    exact
      (rawBetaCircleParameterCauchyHasDerivAt38 B hB c r w hwsphere).differentiableAt.differentiableWithinAt
  exact hd.analyticOnNhd isOpen_ball

end
end NlsGge.GK38
