import QuantumNLS.TerraMultiRound77FiniteKernel

/-! Finite-moment physical/free correction identity in the squared parameter.
This is a partial REG-010 step and does not assert a moment equivalence. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open QuantumNLS.PhysicalTensor QuantumNLS.FreeLimit
open QuantumNLS.TerraMultiRound77FiniteKernel QuantumNLS.Reg010LowBasic
namespace QuantumNLS.TerraMultiRound77CorrectionIdentity

/-- The squared-parameter kernel is the printed regularization times its
fractional weight. -/
theorem kernel_factor (s t x : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (ht : 0 < t) :
    Real.rpowIntegrand₀₁ s t (x^2) =
      t ^ (s-2) * QuantumNLS.RootH1PositiveSpectral.kernel (Real.sqrt t) x := by
  rw [Real.rpowIntegrand₀₁_eq_pow_div ⟨hs0, hs1⟩ ht.le (sq_nonneg x)]
  unfold QuantumNLS.RootH1PositiveSpectral.kernel
  rw [Real.sq_sqrt ht.le]
  have hp := Real.rpow_add ht (s-2) 1
  rw [Real.rpow_one] at hp
  have he : s-2+1 = s-1 := by ring
  rw [he] at hp
  rw [hp]
  ring

/-- Identity for two finite fractional moments. Both moments are assumed
finite here; the all-L² equivalence is a separate open obligation. -/
theorem finite_correction_identity (μ ν : Measure ℝ) [SFinite μ] [SFinite ν]
    (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1)
    (hμ : Integrable (fun x : ℝ => |x| ^ (2*s)) μ)
    (hν : Integrable (fun x : ℝ => |x| ^ (2*s)) ν) :
    (∫ t in Ioi 0, t ^ (s-2) *
      ((∫ x : ℝ, QuantumNLS.RootH1PositiveSpectral.kernel (Real.sqrt t) x ∂μ) -
       (∫ x : ℝ, QuantumNLS.RootH1PositiveSpectral.kernel (Real.sqrt t) x ∂ν))) =
      (∫ t in Ioi 0, Real.rpowIntegrand₀₁ s t 1) *
        ((∫ x : ℝ, |x| ^ (2*s) ∂μ) - (∫ x : ℝ, |x| ^ (2*s) ∂ν)) := by
  let f : ℝ → ℝ → ℝ := fun t x => Real.rpowIntegrand₀₁ s t (x^2)
  have hprodμ := low_kernel_product_integrable μ s hs0 hs1 hμ
  have hprodν := low_kernel_product_integrable ν s hs0 hs1 hν
  have hiμ : Integrable (fun t => ∫ x, f t x ∂μ) (volume.restrict (Ioi 0)) := hprodμ.integral_prod_left
  have hiν : Integrable (fun t => ∫ x, f t x ∂ν) (volume.restrict (Ioi 0)) := hprodν.integral_prod_left
  have heq : ∀ᵐ t ∂(volume.restrict (Ioi 0)),
      t ^ (s-2) * ((∫ x : ℝ, QuantumNLS.RootH1PositiveSpectral.kernel (Real.sqrt t) x ∂μ) -
        (∫ x : ℝ, QuantumNLS.RootH1PositiveSpectral.kernel (Real.sqrt t) x ∂ν)) =
      (∫ x, f t x ∂μ) - (∫ x, f t x ∂ν) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hpoint : f t = fun x => t ^ (s-2) * QuantumNLS.RootH1PositiveSpectral.kernel (Real.sqrt t) x := by
      funext x
      exact kernel_factor s t x hs0 hs1 ht
    rw [hpoint, integral_const_mul, integral_const_mul]
    ring
  rw [integral_congr_ae heq, integral_sub hiμ hiν]
  change (∫ t in Ioi 0, ∫ x, Real.rpowIntegrand₀₁ s t (x^2) ∂μ) -
      (∫ t in Ioi 0, ∫ x, Real.rpowIntegrand₀₁ s t (x^2) ∂ν) = _
  rw [low_finite_moment μ s hs0 hs1 hμ, low_finite_moment ν s hs0 hs1 hν]
  ring

/-- Specialization to the actual physical and free measures and their
existing correction function. -/
theorem physical_free_finite_correction {L κ : ℝ} [Fact (0 < L)]
    (hκ : 0 < κ) (u : L2T L) (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1)
    (hμ : Integrable (fun x : ℝ => |x| ^ (2*s)) (PhysicalQuantumMeasure.measure hκ u))
    (hν : Integrable (fun x : ℝ => |x| ^ (2*s)) (freeMeasure L u)) :
    (∫ t in Ioi 0, t ^ (s-2) * correction κ hκ u (Real.sqrt t)) =
      (∫ t in Ioi 0, Real.rpowIntegrand₀₁ s t 1) *
        ((∫ x : ℝ, |x| ^ (2*s) ∂PhysicalQuantumMeasure.measure hκ u) -
          (∫ x : ℝ, |x| ^ (2*s) ∂freeMeasure L u)) := by
  haveI : IsFiniteMeasure (freeMeasure L u) := free_finite u
  exact finite_correction_identity _ _ s hs0 hs1 hμ hν

#print axioms kernel_factor
#print axioms finite_correction_identity
#print axioms physical_free_finite_correction
end QuantumNLS.TerraMultiRound77CorrectionIdentity
