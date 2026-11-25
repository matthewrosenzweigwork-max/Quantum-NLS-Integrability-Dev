import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option autoImplicit false

/-- On the full height range needed by the source amplitudes, the real
exponential is Lipschitz with the exact dominating constant. -/
theorem actualRealExp_boundedHeight_lipschitz35V1
    (Y₀ a b : ℝ) (hY₀ : 0 ≤ Y₀)
    (ha : a ∈ Set.Icc (-2 * Y₀) (2 * Y₀))
    (hb : b ∈ Set.Icc (-2 * Y₀) (2 * Y₀)) :
    |Real.exp a - Real.exp b| ≤ Real.exp (2 * Y₀) * |a - b| := by
  have hderiv : ∀ x ∈ Set.Icc (-2 * Y₀) (2 * Y₀),
      DifferentiableAt ℝ Real.exp x := by
    intro x hx
    exact Real.differentiableAt_exp
  have hbound : ∀ x ∈ Set.Icc (-2 * Y₀) (2 * Y₀),
      ‖deriv Real.exp x‖ ≤ Real.exp (2 * Y₀) := by
    intro x hx
    rw [Real.deriv_exp, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg x)]
    exact Real.exp_le_exp.mpr hx.2
  have h := Convex.norm_image_sub_le_of_norm_deriv_le hderiv hbound
    (convex_Icc _ _) ha hb
  simpa [Real.norm_eq_abs, abs_sub_comm] using h
