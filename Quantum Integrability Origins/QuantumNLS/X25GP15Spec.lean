import QuantumNLS.Ext025HGP15
/-! integrator-authored trusted spec for EXT-025 contract_GP15 (terra_review r234 ACCEPT): headline statement(s) copied verbatim from Ext025HGP15 (QuantumNLS.Ext025HGP15). -/
noncomputable section
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure
namespace QuantumNLS.X25GP15Spec
open QuantumNLS.Ext025HGP15


set_option maxHeartbeats 8000000 in
theorem contract_GP15_spec :
    (∃! μ : Measure (ℤ → Circle), IsProbabilityMeasure μ ∧ IsMulLeftInvariant μ) ∧
    (∀ μ : Measure (ℤ → Circle), IsProbabilityMeasure μ → IsMulLeftInvariant μ →
      MeasurePreserving (fun x : ℤ → Circle => x⁻¹) μ μ) ∧
    (∀ μ : Measure (ℤ → Circle), IsProbabilityMeasure μ → IsMulLeftInvariant μ →
      ∀ e : (ℤ → Circle) ≃ₜ* (ℤ → Circle), MeasurePreserving e μ μ) ∧
    (∀ μ : Measure (ℤ → Circle), IsProbabilityMeasure μ → IsMulLeftInvariant μ →
      ∀ χ : (ℤ → Circle) →* Circle,
        (∃ F : Finset ℤ, ∀ x y : ℤ → Circle, (∀ i ∈ F, x i = y i) → χ x = χ y) →
        ((χ = 1 → ∫ x, (χ x : ℂ) ∂μ = 1) ∧ (χ ≠ 1 → ∫ x, (χ x : ℂ) ∂μ = 0))) := by
  exact QuantumNLS.Ext025HGP15.contract_GP15 

end QuantumNLS.X25GP15Spec
#print axioms QuantumNLS.X25GP15Spec.contract_GP15_spec
