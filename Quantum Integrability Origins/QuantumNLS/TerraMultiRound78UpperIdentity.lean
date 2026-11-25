import QuantumNLS.TerraMultiRound78UpperKernel
import QuantumNLS.TerraMultiRound77YCorrection
import QuantumNLS.TerraMultiRound74SmallY

/-! Finite upper-order correction identity for H¹ fields. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open QuantumNLS.PhysicalTensor QuantumNLS.FreeLimit QuantumNLS.TranslatedCorrelation
open QuantumNLS.TerraMultiRound78UpperKernel QuantumNLS.TerraMultiRound60Kernel
open QuantumNLS.TerraMultiRound64FieldIdentity QuantumNLS.TerraMultiRound64FreeSobolev
open QuantumNLS.TerraMultiRound61FreeMeasure QuantumNLS.Reg014Moments
namespace QuantumNLS.TerraMultiRound78UpperIdentity

theorem upper_kernel_factor (s t x : ℝ) (hs1 : 1 < s) (hs2 : s < 2) (ht : 0 < t) :
    x^2 * Real.rpowIntegrand₀₁ (s-1) t (x^2) =
      t ^ (s-3) * kernel 2 (Real.sqrt t) x := by
  have hp : s-1 ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith
  rw [Real.rpowIntegrand₀₁_eq_pow_div hp ht.le (sq_nonneg x)]
  unfold kernel
  rw [Real.sq_sqrt ht.le]
  have h := Real.rpow_add ht (s-3) 1
  rw [Real.rpow_one] at h
  have he : s-3+1 = s-1-1 := by ring
  rw [he] at h
  rw [h]
  norm_num
  ring

theorem upper_finite_correction (μ ν : Measure ℝ) [SFinite μ] [SFinite ν]
    (s : ℝ) (hs1 : 1 < s) (hs2 : s < 2)
    (hμ : Integrable (fun x : ℝ => |x| ^ (2*s)) μ)
    (hν : Integrable (fun x : ℝ => |x| ^ (2*s)) ν) :
    (∫ t in Ioi 0, t ^ (s-3) *
      ((∫ x : ℝ, kernel 2 (Real.sqrt t) x ∂μ) -
       (∫ x : ℝ, kernel 2 (Real.sqrt t) x ∂ν))) =
      (∫ t in Ioi 0, Real.rpowIntegrand₀₁ (s-1) t 1) *
        ((∫ x : ℝ, |x| ^ (2*s) ∂μ) - (∫ x : ℝ, |x| ^ (2*s) ∂ν)) := by
  let f : ℝ → ℝ → ℝ := fun t x => x^2 * Real.rpowIntegrand₀₁ (s-1) t (x^2)
  have hiμ : Integrable (fun t => ∫ x, f t x ∂μ) (volume.restrict (Ioi 0)) :=
    (upper_kernel_product_integrable μ s hs1 hs2 hμ).integral_prod_left
  have hiν : Integrable (fun t => ∫ x, f t x ∂ν) (volume.restrict (Ioi 0)) :=
    (upper_kernel_product_integrable ν s hs1 hs2 hν).integral_prod_left
  have heq : ∀ᵐ t ∂(volume.restrict (Ioi 0)),
      t ^ (s-3) * ((∫ x : ℝ, kernel 2 (Real.sqrt t) x ∂μ) -
        (∫ x : ℝ, kernel 2 (Real.sqrt t) x ∂ν)) =
      (∫ x, f t x ∂μ) - (∫ x, f t x ∂ν) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hpoint : f t = fun x => t ^ (s-3) * kernel 2 (Real.sqrt t) x := by
      funext x
      exact upper_kernel_factor s t x hs1 hs2 ht
    rw [hpoint, integral_const_mul, integral_const_mul]
    ring
  rw [integral_congr_ae heq, integral_sub hiμ hiν]
  change (∫ t in Ioi 0, ∫ x, x^2 * Real.rpowIntegrand₀₁ (s-1) t (x^2) ∂μ) -
      (∫ t in Ioi 0, ∫ x, x^2 * Real.rpowIntegrand₀₁ (s-1) t (x^2) ∂ν) = _
  rw [upper_finite_moment μ s hs1 hs2 hμ, upper_finite_moment ν s hs1 hs2 hν]
  ring

#print axioms upper_kernel_factor
#print axioms upper_finite_correction
end QuantumNLS.TerraMultiRound78UpperIdentity
