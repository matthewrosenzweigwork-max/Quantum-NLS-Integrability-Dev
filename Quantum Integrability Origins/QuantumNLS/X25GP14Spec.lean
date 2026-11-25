import QuantumNLS.Ext025LGP14
/-! integrator-authored trusted spec for EXT-025 GP-14 (review record r80 ACCEPT; owner decision 2026-11-17): headline statement(s) copied verbatim from Ext025LGP14 (QuantumNLS.Ext025L). -/
set_option autoImplicit false
universe u v w
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace QuantumNLS.X25GP14Spec
open QuantumNLS.Ext025L


set_option maxHeartbeats 8000000 in
theorem contract_GP14_spec :
    -- (T1) Tonelli, f measurable
    (∀ (X : Type u) (Y : Type v) [MeasurableSpace X] [MeasurableSpace Y]
      (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν] (f : X × Y → ℝ≥0∞),
      Measurable f →
      (∀ x, Measurable (fun y => f (x, y))) ∧ (∀ y, Measurable (fun x => f (x, y))) ∧
      Measurable (fun x => ∫⁻ y, f (x, y) ∂ν) ∧ Measurable (fun y => ∫⁻ x, f (x, y) ∂μ) ∧
      (∫⁻ z, f z ∂μ.prod ν) = ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ ∧
      (∫⁻ z, f z ∂μ.prod ν) = ∫⁻ y, ∫⁻ x, f (x, y) ∂μ ∂ν) ∧
    -- (T2) Tonelli, f only AE-measurable for μ ⊗ ν
    (∀ (X : Type u) (Y : Type v) [MeasurableSpace X] [MeasurableSpace Y]
      (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν] (f : X × Y → ℝ≥0∞),
      AEMeasurable f (μ.prod ν) →
      (∀ᵐ x ∂μ, AEMeasurable (fun y => f (x, y)) ν) ∧
      (∀ᵐ y ∂ν, AEMeasurable (fun x => f (x, y)) μ) ∧
      AEMeasurable (fun x => ∫⁻ y, f (x, y) ∂ν) μ ∧
      AEMeasurable (fun y => ∫⁻ x, f (x, y) ∂μ) ν ∧
      (∫⁻ z, f z ∂μ.prod ν) = ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ ∧
      (∫⁻ z, f z ∂μ.prod ν) = ∫⁻ y, ∫⁻ x, f (x, y) ∂μ ∂ν) ∧
    -- (F) Fubini, f integrable for μ ⊗ ν, with section qualifiers
    (∀ (X : Type u) (Y : Type v) [MeasurableSpace X] [MeasurableSpace Y]
      (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
      (E : Type w) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
      (f : X × Y → E),
      Integrable f (μ.prod ν) →
      (∀ᵐ x ∂μ, Integrable (fun y => f (x, y)) ν) ∧
      (∀ᵐ y ∂ν, Integrable (fun x => f (x, y)) μ) ∧
      Integrable (fun x => ∫ y, f (x, y) ∂ν) μ ∧
      Integrable (fun y => ∫ x, f (x, y) ∂μ) ν ∧
      (∫ z, f z ∂μ.prod ν) = ∫ x, ∫ y, f (x, y) ∂ν ∂μ ∧
      (∫ z, f z ∂μ.prod ν) = ∫ y, ∫ x, f (x, y) ∂μ ∂ν) := by
  exact QuantumNLS.Ext025L.contract_GP14 

end QuantumNLS.X25GP14Spec
#print axioms QuantumNLS.X25GP14Spec.contract_GP14_spec
