import QuantumNLS.Ext025LROOT03
/-! integrator-authored trusted spec for EXT-025 contract_ROOT03 (contract ACCEPT): headline statement(s) copied verbatim from Ext025LROOT03 (QuantumNLS.Ext025L). -/
set_option autoImplicit false
universe u v
set_option maxHeartbeats 1600000
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace QuantumNLS.X25ROOT03Spec
open QuantumNLS.Ext025L


set_option maxHeartbeats 8000000 in
theorem contract_ROOT03_spec :
    ∀ (X : Type u) (Y : Type v) [MeasurableSpace X] [MeasurableSpace Y]
      (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν] (K : X × Y → ℂ),
      AEStronglyMeasurable K (μ.prod ν) → ∀ (A B : ℝ), 0 ≤ A → 0 ≤ B →
      (∀ x, ∫⁻ y, ‖K (x, y)‖ₑ ∂ν ≤ ENNReal.ofReal A) →
      (∀ y, ∫⁻ x, ‖K (x, y)‖ₑ ∂μ ≤ ENNReal.ofReal B) →
      ∃ T : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ, ‖T‖ ≤ Real.sqrt (A * B) ∧
        (∀ g : Lp ℂ 2 ν, (∀ᵐ x ∂μ, Integrable (fun y => K (x, y) * g y) ν) ∧
          (T g : X → ℂ) =ᵐ[μ] fun x => ∫ y, K (x, y) * g y ∂ν) ∧
        (∀ T' : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ,
          (∀ g : Lp ℂ 2 ν, (T' g : X → ℂ) =ᵐ[μ] fun x => ∫ y, K (x, y) * g y ∂ν) → T' = T) ∧
        ((A = 0 ∨ B = 0) → T = 0) := by
  exact QuantumNLS.Ext025L.contract_ROOT03 

end QuantumNLS.X25ROOT03Spec
#print axioms QuantumNLS.X25ROOT03Spec.contract_ROOT03_spec
