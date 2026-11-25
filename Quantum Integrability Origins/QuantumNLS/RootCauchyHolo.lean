import Mathlib
import QuantumNLS.CauchyUniqueness

/-!
# R-C4F43CA8 part (a), stage 1: holomorphy of the Cauchy transform on the upper half-plane

For a finite measure `ρ` on `ℝ` and `Im z > 0`, `z ↦ ∫ (z − t)⁻¹ dρ(t)` (`CauchyUniqueness.cauchyTransform ρ`) is
complex differentiable (dominated differentiation under the integral, dominating constant `4/(Im z₀)²` on the ball
of radius `Im z₀/2`), hence holomorphic and real-analytic on the upper half-plane.

Proved (standard axioms only):
* `cauchyTransform_norm_le`: `‖cauchyTransform ρ z‖ ≤ ρ(ℝ).toReal / Im z` (uniform bound, no HighHalf needed);
* `differentiableAt_cauchyTransform`: complex differentiability at each `z₀` with `Im z₀ > 0`;
* `analyticOnNhd_cauchyTransform`: real-analyticity on `{z | 0 < z.im}`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric Complex

namespace QuantumNLS.RootCauchyHolo

/-- The open upper half-plane. -/
def upperHalf : Set ℂ := {z | 0 < z.im}

theorem isOpen_upperHalf : IsOpen upperHalf :=
  isOpen_lt continuous_const Complex.continuous_im

theorem sub_ofReal_ne_zero {x : ℂ} (hx : 0 < x.im) (t : ℝ) : x - (t : ℂ) ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  linarith

theorem norm_inv_sub_ofReal_le {x : ℂ} (hx : 0 < x.im) (t : ℝ) : ‖(x - (t : ℂ))⁻¹‖ ≤ 1 / x.im := by
  rw [norm_inv, one_div]
  have hi : |x.im| ≤ ‖x - (t : ℂ)‖ := by
    have := Complex.abs_im_le_norm (x - (t : ℂ))
    simpa using this
  have hpos : 0 < ‖x - (t : ℂ)‖ := norm_pos_iff.2 (sub_ofReal_ne_zero hx t)
  have hxim : |x.im| = x.im := abs_of_pos hx
  rw [hxim] at hi
  exact inv_anti₀ hx hi

/-- Uniform bound for the Cauchy transform of a finite measure on the upper half-plane. -/
theorem cauchyTransform_norm_le (ρ : Measure ℝ) [IsFiniteMeasure ρ] {x : ℂ} (hx : 0 < x.im) :
    ‖QuantumNLS.CauchyUniqueness.cauchyTransform ρ x‖ ≤ ρ.real Set.univ / x.im := by
  unfold QuantumNLS.CauchyUniqueness.cauchyTransform
  have hb : ∀ t : ℝ, ‖(x - (t : ℂ))⁻¹‖ ≤ 1 / x.im := fun t => norm_inv_sub_ofReal_le hx t
  have hmeas : AEStronglyMeasurable (fun t : ℝ => (x - (t : ℂ))⁻¹) ρ := by
    apply Continuous.aestronglyMeasurable
    exact (continuous_const.sub Complex.continuous_ofReal).inv₀ (fun t => sub_ofReal_ne_zero hx t)
  have hint : Integrable (fun t : ℝ => (x - (t : ℂ))⁻¹) ρ :=
    (integrable_const (1 / x.im)).mono' hmeas (Eventually.of_forall hb)
  calc ‖∫ t : ℝ, (x - (t : ℂ))⁻¹ ∂ρ‖ ≤ ∫ t : ℝ, ‖(x - (t : ℂ))⁻¹‖ ∂ρ := norm_integral_le_integral_norm _
    _ ≤ ∫ _t : ℝ, 1 / x.im ∂ρ := integral_mono_of_nonneg (Eventually.of_forall fun t => norm_nonneg _)
        (integrable_const _) (Eventually.of_forall hb)
    _ = ρ.real Set.univ / x.im := by
        rw [integral_const, smul_eq_mul, div_eq_mul_one_div]
        ring

/-- Complex differentiability of the Cauchy transform of a finite measure at points of the upper half-plane. -/
theorem differentiableAt_cauchyTransform (ρ : Measure ℝ) [IsFiniteMeasure ρ] {z₀ : ℂ} (hz₀ : 0 < z₀.im) :
    DifferentiableAt ℂ (fun z => QuantumNLS.CauchyUniqueness.cauchyTransform ρ z) z₀ := by
  set ε : ℝ := z₀.im / 2 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  have hball : ∀ x ∈ ball z₀ ε, 0 < x.im := by
    intro x hx
    rw [mem_ball, Complex.dist_eq] at hx
    have h1 := Complex.abs_im_le_norm (x - z₀)
    have h2 : |(x - z₀).im| < ε := lt_of_le_of_lt (by simpa using h1) (by simpa using hx)
    have h3 : (x - z₀).im = x.im - z₀.im := by simp
    rw [h3] at h2
    have := (abs_lt.1 h2).1
    linarith
  -- derivative of `x ↦ (x − t)⁻¹`
  have hderiv : ∀ x t : ℝ, True := fun _ _ => trivial
  have hd : ∀ (x : ℂ) (t : ℝ), 0 < x.im → HasDerivAt (fun y : ℂ => (y - (t : ℂ))⁻¹) (-1 / (x - (t : ℂ)) ^ 2) x := by
    intro x t hx
    have h1 : HasDerivAt (fun y : ℂ => y - (t : ℂ)) 1 x := (hasDerivAt_id x).sub_const (t : ℂ)
    have h2 := h1.inv (sub_ofReal_ne_zero hx t)
    exact h2
  have hbound : ∀ x ∈ ball z₀ ε, ∀ t : ℝ, ‖-1 / (x - (t : ℂ)) ^ 2‖ ≤ 4 / z₀.im ^ 2 := by
    intro x hx t
    have hxi := hball x hx
    have hxi2 : z₀.im / 2 ≤ x.im := by
      rw [mem_ball, Complex.dist_eq] at hx
      have h1 := Complex.abs_im_le_norm (x - z₀)
      have h2 : |(x - z₀).im| < ε := lt_of_le_of_lt (by simpa using h1) (by simpa using hx)
      have h3 : (x - z₀).im = x.im - z₀.im := by simp
      rw [h3] at h2
      have := (abs_lt.1 h2).1
      linarith
    have hn : ‖x - (t : ℂ)‖ ≥ x.im := by
      have h := Complex.abs_im_le_norm (x - (t : ℂ))
      have hi : (x - (t : ℂ)).im = x.im := by simp
      rw [hi, abs_of_pos hxi] at h
      exact h
    have hpos : 0 < x.im := hxi
    have hsq : (z₀.im / 2) ^ 2 ≤ ‖x - (t : ℂ)‖ ^ 2 := by
      have : z₀.im / 2 ≤ ‖x - (t : ℂ)‖ := le_trans hxi2 hn
      exact pow_le_pow_left₀ (by linarith) this 2
    rw [norm_div, norm_neg, norm_one, norm_pow]
    have hnpos : 0 < ‖x - (t : ℂ)‖ := lt_of_lt_of_le hpos hn
    rw [div_le_div_iff₀ (pow_pos hnpos 2) (pow_pos hz₀ 2)]
    nlinarith [hsq]
  have hF_meas : ∀ᶠ x in 𝓝 z₀, AEStronglyMeasurable (fun t : ℝ => (x - (t : ℂ))⁻¹) ρ := by
    filter_upwards [(isOpen_upperHalf).mem_nhds hz₀] with x hx
    apply Continuous.aestronglyMeasurable
    exact (continuous_const.sub Complex.continuous_ofReal).inv₀ (fun t => sub_ofReal_ne_zero hx t)
  have hF_int : Integrable (fun t : ℝ => (z₀ - (t : ℂ))⁻¹) ρ :=
    (integrable_const (1 / z₀.im)).mono' (by
      apply Continuous.aestronglyMeasurable
      exact (continuous_const.sub Complex.continuous_ofReal).inv₀ (fun t => sub_ofReal_ne_zero hz₀ t))
      (Eventually.of_forall fun t => norm_inv_sub_ofReal_le hz₀ t)
  have hF'_meas : AEStronglyMeasurable (fun t : ℝ => -1 / (z₀ - (t : ℂ)) ^ 2) ρ := by
    apply Continuous.aestronglyMeasurable
    exact continuous_const.div ((continuous_const.sub Complex.continuous_ofReal).pow 2)
      (fun t => pow_ne_zero 2 (sub_ofReal_ne_zero hz₀ t))
  have hbd : ∀ᵐ (t : ℝ) ∂ρ, ∀ x ∈ ball z₀ ε, ‖-1 / (x - (t : ℂ)) ^ 2‖ ≤ (fun _ : ℝ => 4 / z₀.im ^ 2) t :=
    Eventually.of_forall fun t x hx => hbound x hx t
  have hdiff : ∀ᵐ (t : ℝ) ∂ρ, ∀ x ∈ ball z₀ ε, HasDerivAt (fun y : ℂ => (y - (t : ℂ))⁻¹) (-1 / (x - (t : ℂ)) ^ 2) x :=
    Eventually.of_forall fun t x hx => hd x t (hball x hx)
  have key := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ρ) (x₀ := z₀)
    (F := fun (x : ℂ) (t : ℝ) => (x - (t : ℂ))⁻¹) (F' := fun (x : ℂ) (t : ℝ) => -1 / (x - (t : ℂ)) ^ 2)
    (bound := fun _ : ℝ => 4 / z₀.im ^ 2) (ball_mem_nhds z₀ hεpos) hF_meas hF_int hF'_meas hbd
    (integrable_const _) hdiff).2
  exact key.differentiableAt

/-- The Cauchy transform of a finite measure is real-analytic on the upper half-plane. -/
theorem analyticOnNhd_cauchyTransform (ρ : Measure ℝ) [IsFiniteMeasure ρ] :
    AnalyticOnNhd ℝ (fun z => QuantumNLS.CauchyUniqueness.cauchyTransform ρ z) upperHalf := by
  have hd : DifferentiableOn ℂ (fun z => QuantumNLS.CauchyUniqueness.cauchyTransform ρ z) upperHalf :=
    fun z hz => (differentiableAt_cauchyTransform ρ hz).differentiableWithinAt
  have hA : AnalyticOnNhd ℂ (fun z => QuantumNLS.CauchyUniqueness.cauchyTransform ρ z) upperHalf :=
    hd.analyticOnNhd isOpen_upperHalf
  intro z hz
  exact (hA z hz).restrictScalars

end QuantumNLS.RootCauchyHolo

#print axioms QuantumNLS.RootCauchyHolo.analyticOnNhd_cauchyTransform
#print axioms QuantumNLS.RootCauchyHolo.cauchyTransform_norm_le
