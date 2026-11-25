import Mathlib
import QuantumNLS.MixedTraceNorm

/-!
# PROP-026 `lem:MP-linearization`: quantitative bounds for the multiplier chart `eq:MP-chart`

New module.  Pure complex analysis, no operators.  For the chart `chartD, chartA, chartLambda` of `MixedTraceNorm`
(`eq:MP-chart`: `d = D (1 + (w²-s²)/D²)^{1/2}`, `a = (w+d)/2`, `λ = c₀ + log(a/A)`, `A = (s+D)/2`), with background data
`d₀ ≤ ‖D‖`, `‖s‖ ≤ s₁`, `a₀ ≤ ‖A‖` and `ρ = rho d₀ s₁ a₀`, for every `w` with `‖w - s‖ < ρ`:

* `q_le`: `‖(w²-s²)/D²‖ ≤ 1/2`, so `1 + q` lies in the slit plane (`Re ≥ 1/2`);
* `sqrt_close`: `‖(1+q)^{1/2} - 1‖ ≤ ‖q‖`;
* `chartA_close`: `‖a(w)/A - 1‖ ≤ 1/2`, so `a/A` lies in the slit plane;
* `norm_chartLambda_le`: `‖λ(w)‖ ≤ ‖c₀‖ + 1`;
* `differentiableOn_chartLambda`: `λ` is complex differentiable on `ball s ρ`.
These are the Taylor-branch statements of the source (`All branches are the Taylor branches at the background`) made quantitative.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

open Complex Metric Set Filter
open QuantumNLS.MixedTraceNorm (chartD chartA chartLambda)

namespace QuantumNLS.MPChartBounds

/-- The chart radius `ρ` for background constants `d₀ ≤ ‖D‖`, `‖s‖ ≤ s₁`, `a₀ ≤ ‖A‖`. -/
def rho (d₀ s₁ a₀ : ℝ) : ℝ := min 1 (min (d₀ ^ 2 / (2 * (2 * s₁ + 1))) (a₀ * d₀ / (d₀ + 2 * s₁ + 1)))

theorem rho_pos {d₀ s₁ a₀ : ℝ} (hd : 0 < d₀) (hs : 0 ≤ s₁) (ha : 0 < a₀) : 0 < rho d₀ s₁ a₀ := by
  unfold rho
  refine lt_min one_pos (lt_min ?_ ?_) <;> positivity

theorem rho_le_one (d₀ s₁ a₀ : ℝ) : rho d₀ s₁ a₀ ≤ 1 := min_le_left _ _

theorem rho_le_d (d₀ s₁ a₀ : ℝ) : rho d₀ s₁ a₀ ≤ d₀ ^ 2 / (2 * (2 * s₁ + 1)) :=
  (min_le_right _ _).trans (min_le_left _ _)

theorem rho_le_a (d₀ s₁ a₀ : ℝ) : rho d₀ s₁ a₀ ≤ a₀ * d₀ / (d₀ + 2 * s₁ + 1) :=
  (min_le_right _ _).trans (min_le_right _ _)

section Bounds

variable {D s A w : ℂ} {d₀ s₁ a₀ : ℝ}

theorem norm_w2_s2_le (hs0 : 0 ≤ s₁) (hs : ‖s‖ ≤ s₁) (hw : ‖w - s‖ < rho d₀ s₁ a₀) :
    ‖w ^ 2 - s ^ 2‖ ≤ rho d₀ s₁ a₀ * (2 * s₁ + 1) := by
  have h1 : w ^ 2 - s ^ 2 = (w + s) * (w - s) := by ring
  rw [h1, norm_mul]
  have h2 : ‖w + s‖ ≤ 2 * s₁ + 1 := by
    have : w + s = (w - s) + 2 * s := by ring
    calc ‖w + s‖ = ‖(w - s) + 2 * s‖ := by rw [this]
      _ ≤ ‖w - s‖ + ‖(2 : ℂ) * s‖ := norm_add_le _ _
      _ ≤ 1 + 2 * s₁ := by
          rw [norm_mul]
          have := rho_le_one d₀ s₁ a₀
          have h3 : ‖(2 : ℂ)‖ = 2 := by simp
          rw [h3]; nlinarith [norm_nonneg s]
      _ = 2 * s₁ + 1 := by ring
  have h3 : 0 ≤ ‖w - s‖ := norm_nonneg _
  calc ‖w + s‖ * ‖w - s‖ ≤ (2 * s₁ + 1) * rho d₀ s₁ a₀ :=
        mul_le_mul h2 hw.le h3 (by linarith)
    _ = rho d₀ s₁ a₀ * (2 * s₁ + 1) := by ring

theorem q_le (hd0 : 0 < d₀) (hs0 : 0 ≤ s₁) (hD : d₀ ≤ ‖D‖) (hs : ‖s‖ ≤ s₁)
    (hw : ‖w - s‖ < rho d₀ s₁ a₀) : ‖(w ^ 2 - s ^ 2) / D ^ 2‖ ≤ 1 / 2 := by
  rw [norm_div, norm_pow]
  have hD2 : d₀ ^ 2 ≤ ‖D‖ ^ 2 := pow_le_pow_left₀ hd0.le hD 2
  have hpos : 0 < ‖D‖ ^ 2 := lt_of_lt_of_le (by positivity) hD2
  rw [div_le_iff₀ hpos]
  have h1 := norm_w2_s2_le (a₀ := a₀) (d₀ := d₀) hs0 hs hw
  have h2 : rho d₀ s₁ a₀ * (2 * s₁ + 1) ≤ d₀ ^ 2 / 2 := by
    have := rho_le_d d₀ s₁ a₀
    have h3 : 0 < 2 * s₁ + 1 := by linarith
    calc rho d₀ s₁ a₀ * (2 * s₁ + 1) ≤ (d₀ ^ 2 / (2 * (2 * s₁ + 1))) * (2 * s₁ + 1) :=
          mul_le_mul_of_nonneg_right this h3.le
      _ = d₀ ^ 2 / 2 := by field_simp
  linarith

theorem one_add_re_pos {q : ℂ} (hq : ‖q‖ ≤ 1 / 2) : 0 < (1 + q).re := by
  have := abs_re_le_norm q
  have h2 := neg_abs_le q.re
  simp only [add_re, one_re]
  linarith

theorem one_add_mem_slit {q : ℂ} (hq : ‖q‖ ≤ 1 / 2) : (1 + q) ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  exact Or.inl (one_add_re_pos hq)

theorem sqrt_close {q : ℂ} (hq : ‖q‖ ≤ 1 / 2) : ‖(1 + q) ^ (1 / 2 : ℂ) - 1‖ ≤ ‖q‖ := by
  have hne : (1 + q) ≠ 0 := slitPlane_ne_zero (one_add_mem_slit hq)
  set r : ℂ := (1 + q) ^ (1 / 2 : ℂ) with hr
  have hr2 : r * r = 1 + q := by
    rw [hr, ← cpow_add _ _ hne]
    norm_num
  have hre1 : 0 < (1 + q).re := one_add_re_pos hq
  have hre : 0 ≤ r.re := by
    rw [hr, cpow_def_of_ne_zero hne, exp_re]
    refine mul_nonneg (Real.exp_pos _).le ?_
    have harg : |(1 + q).arg| < Real.pi / 2 := abs_arg_lt_pi_div_two_iff.2 (Or.inl hre1)
    have : (log (1 + q) * (1 / 2 : ℂ)).im = (1 + q).arg / 2 := by
      simp [log_im, mul_im]; ring
    rw [this]
    apply (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩).le
    · have := neg_abs_le (1 + q).arg; linarith [Real.pi_pos]
    · have := le_abs_self (1 + q).arg; linarith [Real.pi_pos]
  have hr1 : 1 ≤ ‖r + 1‖ := by
    have := re_le_norm (r + 1)
    simp only [add_re, one_re] at this
    linarith
  have hfac : (r - 1) * (r + 1) = q := by linear_combination hr2
  have : ‖r - 1‖ * ‖r + 1‖ = ‖q‖ := by rw [← norm_mul, hfac]
  nlinarith [norm_nonneg (r - 1)]

theorem chartA_close (hd0 : 0 < d₀) (hs0 : 0 ≤ s₁) (ha0 : 0 < a₀) (hD : d₀ ≤ ‖D‖) (hs : ‖s‖ ≤ s₁)
    (hA : a₀ ≤ ‖A‖) (hAd : A = (s + D) / 2) (hw : ‖w - s‖ < rho d₀ s₁ a₀) :
    ‖chartA D s w / A - 1‖ ≤ 1 / 2 := by
  have hq := q_le hd0 hs0 hD hs hw
  have hsq := sqrt_close hq
  have hDpos : 0 < ‖D‖ := lt_of_lt_of_le hd0 hD
  have hApos : 0 < ‖A‖ := lt_of_lt_of_le ha0 hA
  have hAne : A ≠ 0 := norm_pos_iff.1 hApos
  have hdiff : chartA D s w - A = ((w - s) + D * ((1 + (w ^ 2 - s ^ 2) / D ^ 2) ^ (1 / 2 : ℂ) - 1)) / 2 := by
    unfold chartA chartD
    rw [hAd]; ring
  have h1 : chartA D s w / A - 1 = (chartA D s w - A) / A := by field_simp
  rw [h1, norm_div, div_le_iff₀ hApos, hdiff, norm_div]
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2]
  have h3 : ‖D * ((1 + (w ^ 2 - s ^ 2) / D ^ 2) ^ (1 / 2 : ℂ) - 1)‖ ≤ ‖w ^ 2 - s ^ 2‖ / ‖D‖ := by
    rw [norm_mul]
    calc ‖D‖ * ‖(1 + (w ^ 2 - s ^ 2) / D ^ 2) ^ (1 / 2 : ℂ) - 1‖ ≤ ‖D‖ * ‖(w ^ 2 - s ^ 2) / D ^ 2‖ :=
          mul_le_mul_of_nonneg_left hsq (norm_nonneg _)
      _ = ‖w ^ 2 - s ^ 2‖ / ‖D‖ := by
          rw [norm_div, norm_pow]; field_simp
  have h4 := norm_w2_s2_le (a₀ := a₀) (d₀ := d₀) hs0 hs hw
  have h5 : ‖w ^ 2 - s ^ 2‖ / ‖D‖ ≤ rho d₀ s₁ a₀ * (2 * s₁ + 1) / d₀ :=
    calc ‖w ^ 2 - s ^ 2‖ / ‖D‖ ≤ ‖w ^ 2 - s ^ 2‖ / d₀ := div_le_div_of_nonneg_left (norm_nonneg _) hd0 hD
      _ ≤ rho d₀ s₁ a₀ * (2 * s₁ + 1) / d₀ := div_le_div_of_nonneg_right h4 hd0.le
  have h6 : ‖(w - s) + D * ((1 + (w ^ 2 - s ^ 2) / D ^ 2) ^ (1 / 2 : ℂ) - 1)‖ ≤
      rho d₀ s₁ a₀ + rho d₀ s₁ a₀ * (2 * s₁ + 1) / d₀ :=
    (norm_add_le _ _).trans (add_le_add hw.le (h3.trans h5))
  have h7 : rho d₀ s₁ a₀ + rho d₀ s₁ a₀ * (2 * s₁ + 1) / d₀ ≤ a₀ := by
    have hr := rho_le_a d₀ s₁ a₀
    have hden : 0 < d₀ + 2 * s₁ + 1 := by linarith
    have : rho d₀ s₁ a₀ * (d₀ + 2 * s₁ + 1) ≤ a₀ * d₀ := by
      rw [le_div_iff₀ hden] at hr; exact hr
    have e : rho d₀ s₁ a₀ + rho d₀ s₁ a₀ * (2 * s₁ + 1) / d₀ =
        rho d₀ s₁ a₀ * (d₀ + 2 * s₁ + 1) / d₀ := by field_simp; ring
    rw [e, div_le_iff₀ hd0]; linarith
  have h8 : ‖(w - s) + D * ((1 + (w ^ 2 - s ^ 2) / D ^ 2) ^ (1 / 2 : ℂ) - 1)‖ / 2 ≤ 1 / 2 * ‖A‖ := by
    have : ‖(w - s) + D * ((1 + (w ^ 2 - s ^ 2) / D ^ 2) ^ (1 / 2 : ℂ) - 1)‖ ≤ ‖A‖ := h6.trans (h7.trans hA)
    linarith
  exact h8

theorem chartA_div_mem_slit (hd0 : 0 < d₀) (hs0 : 0 ≤ s₁) (ha0 : 0 < a₀) (hD : d₀ ≤ ‖D‖) (hs : ‖s‖ ≤ s₁)
    (hA : a₀ ≤ ‖A‖) (hAd : A = (s + D) / 2) (hw : ‖w - s‖ < rho d₀ s₁ a₀) :
    chartA D s w / A ∈ slitPlane := by
  have h := chartA_close hd0 hs0 ha0 hD hs hA hAd hw
  have := one_add_mem_slit h
  simpa using this

theorem norm_chartLambda_le (c0 : ℂ) (hd0 : 0 < d₀) (hs0 : 0 ≤ s₁) (ha0 : 0 < a₀) (hD : d₀ ≤ ‖D‖)
    (hs : ‖s‖ ≤ s₁) (hA : a₀ ≤ ‖A‖) (hAd : A = (s + D) / 2) (hw : ‖w - s‖ < rho d₀ s₁ a₀) :
    ‖chartLambda c0 D s A w‖ ≤ ‖c0‖ + 1 := by
  have h := chartA_close hd0 hs0 ha0 hD hs hA hAd hw
  have hl := Complex.norm_log_one_add_half_le_self h
  rw [show 1 + (chartA D s w / A - 1) = chartA D s w / A by ring] at hl
  unfold chartLambda
  calc ‖c0 + log (chartA D s w / A)‖ ≤ ‖c0‖ + ‖log (chartA D s w / A)‖ := norm_add_le _ _
    _ ≤ ‖c0‖ + 1 := by linarith [norm_nonneg (chartA D s w / A - 1)]

theorem differentiableAt_chartLambda (c0 : ℂ) (hd0 : 0 < d₀) (hs0 : 0 ≤ s₁) (ha0 : 0 < a₀) (hD : d₀ ≤ ‖D‖)
    (hs : ‖s‖ ≤ s₁) (hA : a₀ ≤ ‖A‖) (hAd : A = (s + D) / 2) (hw : ‖w - s‖ < rho d₀ s₁ a₀) :
    DifferentiableAt ℂ (chartLambda c0 D s A) w := by
  have hDne : D ≠ 0 := norm_pos_iff.1 (lt_of_lt_of_le hd0 hD)
  have hq := q_le hd0 hs0 hD hs hw
  have h1 : DifferentiableAt ℂ (fun w : ℂ => 1 + (w ^ 2 - s ^ 2) / D ^ 2) w := by fun_prop
  have h2 : DifferentiableAt ℂ (fun w : ℂ => (1 + (w ^ 2 - s ^ 2) / D ^ 2) ^ (1 / 2 : ℂ)) w :=
    h1.cpow (differentiableAt_const _) (one_add_mem_slit hq)
  have h3 : DifferentiableAt ℂ (chartA D s) w := by
    unfold chartA chartD
    exact (differentiableAt_id.add (h2.const_mul D)).div_const 2
  have h4 : DifferentiableAt ℂ (fun w => chartA D s w / A) w := h3.div_const A
  have h5 := h4.clog (chartA_div_mem_slit hd0 hs0 ha0 hD hs hA hAd hw)
  exact (differentiableAt_const c0).add h5

end Bounds

end QuantumNLS.MPChartBounds

#print axioms QuantumNLS.MPChartBounds.chartA_close
#print axioms QuantumNLS.MPChartBounds.norm_chartLambda_le
#print axioms QuantumNLS.MPChartBounds.differentiableAt_chartLambda
