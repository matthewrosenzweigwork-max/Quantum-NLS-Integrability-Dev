import QuantumNLS.TerraMultiRound77FiniteKernel

/-! Fubini for the finite upper fractional moment. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace QuantumNLS.TerraMultiRound78UpperKernel

theorem upper_kernel_product_integrable (μ : Measure ℝ) [SFinite μ]
    (s : ℝ) (hs1 : 1 < s) (hs2 : s < 2)
    (hm : Integrable (fun x : ℝ => |x| ^ (2*s)) μ) :
    Integrable (fun z : ℝ × ℝ => z.2^2 * Real.rpowIntegrand₀₁ (s-1) z.1 (z.2^2))
      ((volume.restrict (Ioi 0)).prod μ) := by
  let C : ℝ := ∫ t in Ioi 0, Real.rpowIntegrand₀₁ (s-1) t 1
  have hp : s-1 ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith
  have hmeas : Measurable (fun z : ℝ × ℝ => z.2^2 * Real.rpowIntegrand₀₁ (s-1) z.1 (z.2^2)) := by
    unfold Real.rpowIntegrand₀₁
    fun_prop
  apply (integrable_prod_iff' hmeas.aestronglyMeasurable).2
  constructor
  · exact Filter.Eventually.of_forall (fun x => (Real.integrableOn_rpowIntegrand₀₁_Ioi hp (sq_nonneg x)).const_mul (x^2))
  · have heq : (fun x : ℝ => ∫ t in Ioi 0, ‖x^2 * Real.rpowIntegrand₀₁ (s-1) t (x^2)‖) =
        fun x => C * |x| ^ (2*s) := by
      funext x
      have hnorm : (∫ t in Ioi 0, ‖x^2 * Real.rpowIntegrand₀₁ (s-1) t (x^2)‖) =
          ∫ t in Ioi 0, x^2 * Real.rpowIntegrand₀₁ (s-1) t (x^2) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg x) (Real.rpowIntegrand₀₁_nonneg hp.1 ht.le (sq_nonneg x)))]
      rw [hnorm, integral_const_mul, Real.integral_rpowIntegrand₀₁_eq_rpow_mul_const hp (sq_nonneg x)]
      have hx : x^2 * (x^2)^(s-1) = |x| ^ (2*s) := by
        by_cases hx0 : x = 0
        · subst x; simp [Real.zero_rpow (by linarith : (2*s : ℝ) ≠ 0)]
        · have he : x^2 = |x|^(2:ℝ) := by rw [Real.rpow_two, sq_abs]
          rw [he, ← Real.rpow_mul (abs_nonneg x), ← Real.rpow_add (abs_pos.mpr hx0)]
          congr 1 <;> ring
      rw [← mul_assoc, hx]
      dsimp [C]
      ring
    rw [heq]
    exact hm.const_mul C

theorem upper_finite_moment (μ : Measure ℝ) [SFinite μ]
    (s : ℝ) (hs1 : 1 < s) (hs2 : s < 2)
    (hm : Integrable (fun x : ℝ => |x| ^ (2*s)) μ) :
    (∫ t in Ioi 0, ∫ x : ℝ, x^2 * Real.rpowIntegrand₀₁ (s-1) t (x^2) ∂μ) =
      (∫ t in Ioi 0, Real.rpowIntegrand₀₁ (s-1) t 1) * (∫ x : ℝ, |x| ^ (2*s) ∂μ) := by
  have hi := upper_kernel_product_integrable μ s hs1 hs2 hm
  rw [integral_integral_swap hi]
  have hp : s-1 ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith
  have heq : (fun x : ℝ => ∫ t in Ioi 0, x^2 * Real.rpowIntegrand₀₁ (s-1) t (x^2)) =
      fun x => (∫ t in Ioi 0, Real.rpowIntegrand₀₁ (s-1) t 1) * |x| ^ (2*s) := by
    funext x
    rw [integral_const_mul, Real.integral_rpowIntegrand₀₁_eq_rpow_mul_const hp (sq_nonneg x)]
    by_cases hx0 : x = 0
    · subst x; simp [Real.zero_rpow (by linarith : (2*s : ℝ) ≠ 0)]
    · have hx : x^2 * (x^2)^(s-1) = |x| ^ (2*s) := by
        have he : x^2 = |x|^(2:ℝ) := by rw [Real.rpow_two, sq_abs]
        rw [he, ← Real.rpow_mul (abs_nonneg x), ← Real.rpow_add (abs_pos.mpr hx0)]
        congr 1 <;> ring
      rw [← mul_assoc, hx]
      ring
  rw [heq, integral_const_mul]

#print axioms upper_kernel_product_integrable
#print axioms upper_finite_moment
end QuantumNLS.TerraMultiRound78UpperKernel
