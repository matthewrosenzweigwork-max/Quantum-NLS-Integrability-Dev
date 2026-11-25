import Mathlib

                                                                                                    
                                                                                   
set_option autoImplicit false

noncomputable section
open MeasureTheory Set Filter

namespace NlsGge.ThirdConsultation.I.I013A

/-- A pointwise bound `|F x| ≤ M` on `|x| ≤ R` and `|F x|·|x| ≤ K` on `R ≤ |x|` (with `R ≥ 1`)
gives the weighted bound `F(x)^2 (1+x^2) ≤ M^2 (1+R^2) + 2K^2` everywhere. -/
theorem sq_weight_bound (F : ℝ → ℝ) (M K R : ℝ) (hR : 1 ≤ R)
    (h1 : ∀ x : ℝ, |x| ≤ R → |F x| ≤ M)
    (h2 : ∀ x : ℝ, R ≤ |x| → |F x| * |x| ≤ K) (x : ℝ) :
    F x ^ 2 * (1 + x ^ 2) ≤ M ^ 2 * (1 + R ^ 2) + 2 * K ^ 2 := by
  have hM : 0 ≤ M := le_trans (abs_nonneg (F 0)) (h1 0 (by rw [abs_zero]; linarith))
  by_cases hx : |x| ≤ R
  · have hF : |F x| ≤ M := h1 x hx
    have hFsq : F x ^ 2 ≤ M ^ 2 := by
      nlinarith [abs_nonneg (F x), sq_abs (F x)]
    have hx2 : x ^ 2 ≤ R ^ 2 := by
      nlinarith [abs_nonneg x, sq_abs x]
    have h3 : F x ^ 2 * (1 + x ^ 2) ≤ M ^ 2 * (1 + R ^ 2) :=
      mul_le_mul hFsq (by linarith) (by positivity) (by positivity)
    have h4 : 0 ≤ 2 * K ^ 2 := by positivity
    linarith
  · push_neg at hx
    have ha : |F x| * |x| ≤ K := h2 x hx.le
    have ha0 : 0 ≤ |F x| * |x| := by positivity
    have hsq : (|F x| * |x|) ^ 2 ≤ K ^ 2 := by
      nlinarith [mul_le_mul ha ha ha0 (ha0.trans ha)]
    have e : (|F x| * |x|) ^ 2 = F x ^ 2 * x ^ 2 := by
      rw [mul_pow, sq_abs, sq_abs]
    have hx1 : 1 ≤ x ^ 2 := by
      nlinarith [abs_nonneg x, sq_abs x]
    have hF2 : F x ^ 2 ≤ F x ^ 2 * x ^ 2 := le_mul_of_one_le_right (sq_nonneg _) hx1
    have h5 : F x ^ 2 * (1 + x ^ 2) ≤ 2 * K ^ 2 := by
      calc F x ^ 2 * (1 + x ^ 2) = F x ^ 2 + F x ^ 2 * x ^ 2 := by ring
        _ ≤ F x ^ 2 * x ^ 2 + F x ^ 2 * x ^ 2 := by linarith
        _ = 2 * (|F x| * |x|) ^ 2 := by rw [e]; ring
        _ ≤ 2 * K ^ 2 := by linarith
    have h6 : 0 ≤ M ^ 2 * (1 + R ^ 2) := by positivity
    linarith

/-- Square-integrability from the weighted pointwise bound `F(x)^2 (1+x^2) ≤ C`. -/
theorem memLp_two_of_sq_weight (F : ℝ → ℝ) (hF : AEStronglyMeasurable F volume) (C : ℝ)
    (hC : ∀ x : ℝ, F x ^ 2 * (1 + x ^ 2) ≤ C) : MemLp F 2 volume := by
  rw [memLp_two_iff_integrable_sq hF]
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul C) (hF.pow 2) ?_
  refine Eventually.of_forall fun x => ?_
  have hpos : (0:ℝ) < 1 + x ^ 2 := by positivity
  show ‖F x ^ 2‖ ≤ C * (1 + x ^ 2)⁻¹
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← div_eq_mul_inv, le_div_iff₀ hpos]
  exact hC x

end NlsGge.ThirdConsultation.I.I013A

end
