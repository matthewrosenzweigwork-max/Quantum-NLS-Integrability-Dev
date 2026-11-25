import NlsGge.Atomic.LIB.LIB010

set_option autoImplicit false
noncomputable section

open Filter Metric Topology

namespace NlsGge.Atomic.G4

universe u

/-- Cauchy's sharp first-derivative estimate for an analytic Banach-valued
map on an open ball.  The smaller closed balls are supplied to LIB-010, so no
analyticity on the boundary of the original open ball is assumed. -/
theorem norm_fderiv_le_of_ball_bound {E F : Type u}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {f : E → F} {u : E} {r M : ℝ}
    (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (Metric.ball u r))
    (hM : ∀ v ∈ Metric.ball u r, ‖f v‖ ≤ M) :
    ‖fderiv ℂ f u‖ ≤ M / r := by
  let R : ℕ → ℝ := fun n => r * (((n : ℝ) + 1) / ((n : ℝ) + 2))
  have hM0 : 0 ≤ M := by
    have hu : u ∈ Metric.ball u r := Metric.mem_ball_self hr
    exact (norm_nonneg (f u)).trans (hM u hu)
  have hRpos (n : ℕ) : 0 < R n := by
    dsimp [R]
    apply mul_pos hr
    exact div_pos (by positivity) (by positivity)
  have hRlt (n : ℕ) : R n < r := by
    dsimp [R]
    have hden : 0 < (n : ℝ) + 2 := by positivity
    have hfrac : ((n : ℝ) + 1) / ((n : ℝ) + 2) < 1 := by
      apply (div_lt_one hden).2
      have hn : (0 : ℝ) ≤ n := by positivity
      linarith
    calc
      r * (((n : ℝ) + 1) / ((n : ℝ) + 2)) < r * 1 :=
        mul_lt_mul_of_pos_left hfrac hr
      _ = r := mul_one r
  have hsmall (n : ℕ) : Metric.closedBall u (R n) ⊆ Metric.ball u r := by
    intro v hv
    change dist v u ≤ R n at hv
    change dist v u < r
    exact lt_of_le_of_lt hv (hRlt n)
  have hquotBound (n : ℕ) : ‖fderiv ℂ f u‖ ≤ M / R n := by
    have hfa : AnalyticOnNhd ℂ f (Metric.closedBall u (R n)) := hf.mono (hsmall n)
    have hMb : ∀ v ∈ Metric.closedBall u (R n), ‖f v‖ ≤ M :=
      fun v hv => hM v (hsmall n hv)
    have hMs : ∀ v ∈ Metric.sphere u (R n), ‖f v‖ ≤ M := by
      intro v hv
      exact hMb v (Metric.sphere_subset_closedBall hv)
    refine ContinuousLinearMap.opNorm_le_of_unit_norm
      (div_nonneg hM0 (hRpos n).le) ?_
    intro v hv
    exact NlsGge.Atomic.LIB.cauchy_fderiv_center_unit_direction_bound
      hfa hMs (hRpos n) hv
  have hden : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 2)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hden
  have hratioEq :
      (fun n : ℕ => ((n : ℝ) + 1) / ((n : ℝ) + 2)) =
        (fun n : ℕ => 1 - (((n : ℝ) + 2)⁻¹)) := by
    funext n
    have hden0 : (n : ℝ) + 2 ≠ 0 := by positivity
    field_simp
    <;> ring
  have hratio : Tendsto
      (fun n : ℕ => ((n : ℝ) + 1) / ((n : ℝ) + 2)) atTop (𝓝 1) := by
    rw [hratioEq]
    simpa using tendsto_const_nhds.sub hinv
  have hRlim : Tendsto R atTop (𝓝 r) := by
    simpa [R] using tendsto_const_nhds.mul hratio
  have hquotlim : Tendsto (fun n : ℕ => M / R n) atTop (𝓝 (M / r)) := by
    change Tendsto ((fun _ : ℕ => M) / R) atTop (𝓝 (M / r))
    exact tendsto_const_nhds.div hRlim hr.ne'
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds hquotlim hquotBound

end NlsGge.Atomic.G4
