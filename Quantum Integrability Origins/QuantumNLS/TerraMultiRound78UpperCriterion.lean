import QuantumNLS.TerraMultiRound78UpperIdentity

/-! Positive upper kernel detects finite fractional moments without subtraction. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open QuantumNLS.TerraMultiRound78UpperIdentity QuantumNLS.TerraMultiRound78UpperKernel
open QuantumNLS.TerraMultiRound61MomentRecurrence
namespace QuantumNLS.TerraMultiRound78UpperCriterion

theorem upper_outer_integrable_iff (μ : Measure ℝ) [IsFiniteMeasure μ]
    (s : ℝ) (hs1 : 1 < s) (hs2 : s < 2)
    (hsecond : Integrable (fun x : ℝ => x^2) μ) :
    Integrable (fun t : ℝ => ∫ x : ℝ, x^2 * Real.rpowIntegrand₀₁ (s-1) t (x^2) ∂μ)
      (volume.restrict (Ioi 0)) ↔
    Integrable (fun x : ℝ => |x| ^ (2*s)) μ := by
  let f : ℝ × ℝ → ℝ := fun z => z.2^2 * Real.rpowIntegrand₀₁ (s-1) z.1 (z.2^2)
  let C : ℝ := ∫ t in Ioi 0, Real.rpowIntegrand₀₁ (s-1) t 1
  have hp : s-1 ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith
  have hC : 0 < C := Real.integral_rpowIntegrand₀₁_one_pos hp
  have hf : Measurable f := by
    dsimp [f]
    unfold Real.rpowIntegrand₀₁
    fun_prop
  constructor
  · intro hout
    have hsection : ∀ᵐ t ∂(volume.restrict (Ioi 0)), Integrable (fun x => f (t,x)) μ := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have hker := kernel_integrable_succ μ 1 (Real.sqrt t) (Real.sqrt_pos.2 ht) (by simpa using hsecond)
      have heq : (fun x => f (t,x)) = fun x => t ^ (s-3) *
          QuantumNLS.TerraMultiRound60Kernel.kernel 2 (Real.sqrt t) x := by
        funext x
        exact upper_kernel_factor s t x hs1 hs2 ht
      rw [heq]
      exact hker.const_mul _
    have hnorm : (fun t => ∫ x, ‖f (t,x)‖ ∂μ) =ᵐ[volume.restrict (Ioi 0)]
        (fun t => ∫ x, f (t,x) ∂μ) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      apply integral_congr_ae
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg x)
        (Real.rpowIntegrand₀₁_nonneg hp.1 ht.le (sq_nonneg x)))]
    have hprod : Integrable f ((volume.restrict (Ioi 0)).prod μ) :=
      (integrable_prod_iff hf.aestronglyMeasurable).2 ⟨hsection, hout.congr hnorm.symm⟩
    have hscaled := hprod.integral_norm_prod_right
    have heq : (fun x : ℝ => ∫ t in Ioi 0, ‖f (t,x)‖) =
        fun x => C * |x| ^ (2*s) := by
      funext x
      have hn : (∫ t in Ioi 0, ‖f (t,x)‖) = ∫ t in Ioi 0, f (t,x) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg x)
          (Real.rpowIntegrand₀₁_nonneg hp.1 ht.le (sq_nonneg x)))]
      rw [hn]
      dsimp [f]
      rw [integral_const_mul, Real.integral_rpowIntegrand₀₁_eq_rpow_mul_const hp (sq_nonneg x)]
      by_cases hx0 : x = 0
      · subst x; simp [Real.zero_rpow (by linarith : (2*s : ℝ) ≠ 0)]
      · have hx : x^2 * (x^2)^(s-1) = |x| ^ (2*s) := by
          have he : x^2 = |x|^(2:ℝ) := by rw [Real.rpow_two, sq_abs]
          rw [he, ← Real.rpow_mul (abs_nonneg x), ← Real.rpow_add (abs_pos.mpr hx0)]
          congr 1 <;> ring
        rw [← mul_assoc, hx]
        dsimp [C]
        ring
    rw [heq] at hscaled
    have h := hscaled.const_mul C⁻¹
    have he : (fun x : ℝ => C⁻¹ * (C * |x| ^ (2*s))) = (fun x => |x| ^ (2*s)) := by
      funext x
      field_simp
    rw [he] at h
    exact h
  · intro hm
    exact (upper_kernel_product_integrable μ s hs1 hs2 hm).integral_prod_left

#print axioms upper_outer_integrable_iff
end QuantumNLS.TerraMultiRound78UpperCriterion
