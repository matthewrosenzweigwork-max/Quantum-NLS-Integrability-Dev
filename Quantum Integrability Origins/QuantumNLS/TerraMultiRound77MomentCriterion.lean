import QuantumNLS.TerraMultiRound77CorrectionIdentity

/-! Finiteness criterion for the positive low-order kernel. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open QuantumNLS.TerraMultiRound77FiniteKernel QuantumNLS.TerraMultiRound77CorrectionIdentity
namespace QuantumNLS.TerraMultiRound77MomentCriterion

/-- The outer regularization is integrable exactly when the corresponding
fractional power moment is integrable. This does not assume a moment identity. -/
theorem low_outer_integrable_iff (μ : Measure ℝ) [IsFiniteMeasure μ]
    (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    Integrable (fun t : ℝ => ∫ x : ℝ, Real.rpowIntegrand₀₁ s t (x^2) ∂μ)
      (volume.restrict (Ioi 0)) ↔
    Integrable (fun x : ℝ => |x| ^ (2*s)) μ := by
  let f : ℝ × ℝ → ℝ := fun z => Real.rpowIntegrand₀₁ s z.1 (z.2^2)
  let C : ℝ := ∫ t in Ioi 0, Real.rpowIntegrand₀₁ s t 1
  have hp : s ∈ Ioo (0 : ℝ) 1 := ⟨hs0, hs1⟩
  have hC : 0 < C := Real.integral_rpowIntegrand₀₁_one_pos hp
  have hf : Measurable f := by
    dsimp [f]
    unfold Real.rpowIntegrand₀₁
    fun_prop
  constructor
  · intro hout
    have hsection : ∀ᵐ t ∂(volume.restrict (Ioi 0)), Integrable (fun x => f (t,x)) μ := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have hker := QuantumNLS.RootH1PositiveSpectral.kernel_integrable (Real.sqrt_pos.2 ht) μ
      have heq : (fun x => f (t,x)) = fun x => t ^ (s-2) *
          QuantumNLS.RootH1PositiveSpectral.kernel (Real.sqrt t) x := by
        funext x
        exact kernel_factor s t x hs0 hs1 ht
      rw [heq]
      exact hker.const_mul _
    have hnorm : (fun t => ∫ x, ‖f (t,x)‖ ∂μ) =ᵐ[volume.restrict (Ioi 0)]
        (fun t => ∫ x, f (t,x) ∂μ) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      apply integral_congr_ae
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpowIntegrand₀₁_nonneg hs0 ht.le (sq_nonneg x))]
    have hprod : Integrable f ((volume.restrict (Ioi 0)).prod μ) :=
      (integrable_prod_iff hf.aestronglyMeasurable).2 ⟨hsection, hout.congr hnorm.symm⟩
    have hscaled := hprod.integral_norm_prod_right
    have heq : (fun x : ℝ => ∫ t in Ioi 0, ‖f (t,x)‖) =
        fun x => C * |x| ^ (2*s) := by
      funext x
      have hn : (∫ t in Ioi 0, ‖f (t,x)‖) = ∫ t in Ioi 0, f (t,x) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpowIntegrand₀₁_nonneg hs0 ht.le (sq_nonneg x))]
      rw [hn]
      have h := Real.integral_rpowIntegrand₀₁_eq_rpow_mul_const hp (sq_nonneg x)
      have hx : (x^2)^s = |x| ^ (2*s) := by
        rw [Real.rpow_mul (abs_nonneg x), Real.rpow_two, sq_abs]
      rw [hx] at h
      dsimp [f, C]
      linarith
    rw [heq] at hscaled
    have h := hscaled.const_mul C⁻¹
    have he : (fun x : ℝ => C⁻¹ * (C * |x| ^ (2*s))) = (fun x => |x| ^ (2*s)) := by
      funext x
      field_simp
    rw [he] at h
    exact h
  · intro hm
    exact (low_kernel_product_integrable μ s hs0 hs1 hm).integral_prod_left

#print axioms low_outer_integrable_iff
end QuantumNLS.TerraMultiRound77MomentCriterion
