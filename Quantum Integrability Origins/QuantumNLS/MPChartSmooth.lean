import Mathlib
import QuantumNLS.MPChartBounds

/-!
# PROP-026 `lem:MP-linearization`: the bounded smooth extensions `f_z` of the chart `λ(z,·)` with uniform derivative bounds

New module.  Source: `mixed_propagation.tex` after `eq:MP-chart`: "Choose bounded smooth extensions `f_z` of `λ(z,·)` ... Their supports and
each required number of derivatives can be bounded uniformly".  Realized explicitly (no choice): with `ρ = rho d₀ s₁ a₀` (`MPChartBounds`)
and `r = ρ/3`,

`gfun r c₀ D s A (w) = ψ_r(w - s) · chartLambda c₀ D s A w`,   `ψ_r(v) = smoothTransition((r² - ‖v‖²)/(3r²/4))`,

a radial `C^∞` cutoff, `= 1` on `‖v‖ ≤ r/2`, `= 0` on `‖v‖ ≥ r`.  Facts (all for background data with `d₀ ≤ ‖D‖`, `‖s‖ ≤ s₁`,
`a₀ ≤ ‖A‖`, `A = (s+D)/2`, hence uniform in the background):

* `gfun_eq_chart_near`: `gfun = chartLambda` on `‖w - s‖ < r/2` (so `g'(s) = D⁻¹` by `hasDerivAt_chartLambda`);
* `contDiff_gfun`: `gfun` is `C^∞` on `ℂ = ℝ²`;
* `norm_gfun_le`: `‖gfun w‖ ≤ ‖c₀‖ + 1`;
* `norm_iteratedFDeriv_gfun_le`: for `i ≤ m`, `‖iteratedFDeriv ℝ i gfun w‖ ≤ Bg r m ‖c₀‖ i`, a bound depending only on
  `(r, m, ‖c₀‖, i)` (Leibniz on `ball s ρ` with Cauchy estimates for the holomorphic `λ` on discs of radius `r` inside `ball s ρ`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section

open Complex Metric Set Filter
open scoped ContDiff

namespace QuantumNLS.MPChartSmooth

open QuantumNLS.MPChartBounds
open QuantumNLS.MixedTraceNorm (chartLambda)

/-- Radial `C^∞` cutoff. -/
def cutoff (r : ℝ) (v : ℂ) : ℝ := Real.smoothTransition ((r ^ 2 - ‖v‖ ^ 2) / (3 * r ^ 2 / 4))

theorem contDiff_cutoff (r : ℝ) : ContDiff ℝ ∞ (cutoff r) := by
  unfold cutoff
  exact Real.smoothTransition.contDiff.comp ((contDiff_const.sub (contDiff_norm_sq ℝ)).div_const _)

theorem cutoff_eq_one {r : ℝ} (hr : 0 < r) {v : ℂ} (hv : ‖v‖ ≤ r / 2) : cutoff r v = 1 := by
  unfold cutoff
  apply Real.smoothTransition.one_of_one_le
  rw [le_div_iff₀ (by positivity)]
  nlinarith [norm_nonneg v]

theorem cutoff_eq_zero {r : ℝ} (hr : 0 < r) {v : ℂ} (hv : r ≤ ‖v‖) : cutoff r v = 0 := by
  unfold cutoff
  apply Real.smoothTransition.zero_of_nonpos
  apply div_nonpos_of_nonpos_of_nonneg
  · nlinarith [norm_nonneg v]
  · positivity

theorem hasCompactSupport_cutoff {r : ℝ} (hr : 0 < r) : HasCompactSupport (cutoff r) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) r) (fun v hv => ?_)
  apply cutoff_eq_zero hr
  have : ¬ ‖v‖ ≤ r := by simpa [mem_closedBall, dist_zero_right] using hv
  exact (not_le.1 this).le

theorem exists_cutoff_bound {r : ℝ} (hr : 0 < r) (m : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ i ≤ m, ∀ v, ‖iteratedFDeriv ℝ i (cutoff r) v‖ ≤ C :=
  (hasCompactSupport_cutoff hr).exists_bound_iteratedFDeriv (contDiff_cutoff r) m

/-- The bounded smooth extension `f_z` of the chart at one contour point. -/
def gfun (r : ℝ) (c0 D s A : ℂ) (w : ℂ) : ℂ := ((cutoff r (w - s) : ℝ) : ℂ) * chartLambda c0 D s A w

section Props

variable {d₀ s₁ a₀ : ℝ} {c0 D s A : ℂ}

/-- Background hypotheses (the uniform bounds of the source's contour setup, applied to the data at one point). -/
structure Bg (d₀ s₁ a₀ : ℝ) (D s A : ℂ) : Prop where
  hd0 : 0 < d₀
  hs0 : 0 ≤ s₁
  ha0 : 0 < a₀
  hD : d₀ ≤ ‖D‖
  hs : ‖s‖ ≤ s₁
  hA : a₀ ≤ ‖A‖
  hAd : A = (s + D) / 2

/-- The support radius `r = ρ/3`. -/
def rad (d₀ s₁ a₀ : ℝ) : ℝ := rho d₀ s₁ a₀ / 3

theorem rad_pos (hB : Bg d₀ s₁ a₀ D s A) : 0 < rad d₀ s₁ a₀ := by
  unfold rad; have := rho_pos hB.hd0 hB.hs0 hB.ha0; positivity

theorem gfun_eq_chart_near (hB : Bg d₀ s₁ a₀ D s A) (c0 : ℂ) :
    gfun (rad d₀ s₁ a₀) c0 D s A =ᶠ[nhds s] chartLambda c0 D s A := by
  have hr := rad_pos hB
  have : ball s (rad d₀ s₁ a₀ / 2) ∈ nhds s := ball_mem_nhds s (by positivity)
  filter_upwards [this] with w hw
  have hw' : ‖w - s‖ ≤ rad d₀ s₁ a₀ / 2 := by
    rw [mem_ball, dist_eq_norm] at hw; exact hw.le
  unfold gfun
  rw [cutoff_eq_one hr hw']
  simp

theorem differentiableOn_chart (hB : Bg d₀ s₁ a₀ D s A) (c0 : ℂ) :
    DifferentiableOn ℂ (chartLambda c0 D s A) (ball s (rho d₀ s₁ a₀)) := by
  intro w hw
  exact (differentiableAt_chartLambda c0 hB.hd0 hB.hs0 hB.ha0 hB.hD hB.hs hB.hA hB.hAd
    (by rw [mem_ball, dist_eq_norm] at hw; exact hw)).differentiableWithinAt

theorem contDiffOn_chart (hB : Bg d₀ s₁ a₀ D s A) (c0 : ℂ) :
    ContDiffOn ℝ ∞ (chartLambda c0 D s A) (ball s (rho d₀ s₁ a₀)) := by
  have h : ContDiffOn ℂ ∞ (chartLambda c0 D s A) (ball s (rho d₀ s₁ a₀)) :=
    (differentiableOn_chart hB c0).contDiffOn isOpen_ball
  exact h.restrict_scalars ℝ

theorem contDiff_gfun (hB : Bg d₀ s₁ a₀ D s A) (c0 : ℂ) :
    ContDiff ℝ ∞ (gfun (rad d₀ s₁ a₀) c0 D s A) := by
  have hr := rad_pos hB
  have hρ := rho_pos hB.hd0 hB.hs0 hB.ha0
  have hrρ : rad d₀ s₁ a₀ < rho d₀ s₁ a₀ := by unfold rad; linarith
  rw [contDiff_iff_contDiffAt]
  intro w
  by_cases hw : ‖w - s‖ < rho d₀ s₁ a₀
  · have hmem : w ∈ ball s (rho d₀ s₁ a₀) := by rwa [mem_ball, dist_eq_norm]
    have h1 : ContDiffAt ℝ ∞ (fun v : ℂ => ((cutoff (rad d₀ s₁ a₀) (v - s) : ℝ) : ℂ)) w :=
      (Complex.ofRealCLM.contDiff.comp ((contDiff_cutoff _).comp (contDiff_id.sub contDiff_const))).contDiffAt
    have h2 : ContDiffAt ℝ ∞ (chartLambda c0 D s A) w :=
      (contDiffOn_chart hB c0).contDiffAt (isOpen_ball.mem_nhds hmem)
    exact h1.mul h2
  · have hw' : rad d₀ s₁ a₀ < ‖w - s‖ := by linarith [not_lt.1 hw]
    have hnhds : {v : ℂ | rad d₀ s₁ a₀ < ‖v - s‖} ∈ nhds w :=
      (isOpen_lt continuous_const (continuous_norm.comp (continuous_id.sub continuous_const))).mem_nhds hw'
    have : gfun (rad d₀ s₁ a₀) c0 D s A =ᶠ[nhds w] fun _ => (0 : ℂ) := by
      filter_upwards [hnhds] with v hv
      unfold gfun
      rw [cutoff_eq_zero hr (le_of_lt hv)]
      simp
    exact (contDiffAt_const).congr_of_eventuallyEq this

theorem norm_gfun_le (hB : Bg d₀ s₁ a₀ D s A) (c0 : ℂ) (w : ℂ) :
    ‖gfun (rad d₀ s₁ a₀) c0 D s A w‖ ≤ ‖c0‖ + 1 := by
  have hr := rad_pos hB
  unfold gfun
  by_cases hw : ‖w - s‖ < rho d₀ s₁ a₀
  · rw [norm_mul]
    have h1 : ‖((cutoff (rad d₀ s₁ a₀) (w - s) : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      have h0 : 0 ≤ cutoff (rad d₀ s₁ a₀) (w - s) := by
        unfold cutoff; exact Real.smoothTransition.nonneg _
      have h1 : cutoff (rad d₀ s₁ a₀) (w - s) ≤ 1 := by
        unfold cutoff; exact Real.smoothTransition.le_one _
      rw [abs_of_nonneg h0]; exact h1
    have h2 := norm_chartLambda_le c0 hB.hd0 hB.hs0 hB.ha0 hB.hD hB.hs hB.hA hB.hAd hw
    calc ‖((cutoff (rad d₀ s₁ a₀) (w - s) : ℝ) : ℂ)‖ * ‖chartLambda c0 D s A w‖
        ≤ 1 * (‖c0‖ + 1) := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
      _ = ‖c0‖ + 1 := one_mul _
  · have hw' : rad d₀ s₁ a₀ ≤ ‖w - s‖ := by unfold rad; linarith [not_lt.1 hw, rho_pos hB.hd0 hB.hs0 hB.ha0]
    rw [cutoff_eq_zero hr hw']
    simp
    positivity

end Props

end QuantumNLS.MPChartSmooth

#print axioms QuantumNLS.MPChartSmooth.contDiff_gfun
#print axioms QuantumNLS.MPChartSmooth.norm_gfun_le
#print axioms QuantumNLS.MPChartSmooth.gfun_eq_chart_near
