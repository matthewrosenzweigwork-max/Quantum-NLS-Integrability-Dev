import QuantumNLS.Ext025GP16R27m
/-! integrator-authored trusted spec for EXT-025 contract_GP16_fixed (contract ACCEPT): headline statement(s) copied verbatim from Ext025GP16R27m (QuantumNLS.Ext025GP16R27m). -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal
namespace QuantumNLS.X25GP16Spec
open QuantumNLS.Ext025GP16R27m
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 8000000 in
theorem contract_GP16_fixed_spec :
    -- interval case: strongly measurable integrand with integrable norm
    (∀ {X E F : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
      [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
      (μ : Measure X) (f : X → E),
      AEStronglyMeasurable f μ → Integrable (fun x => ‖f x‖) μ →
      Integrable f μ ∧ ‖∫ x, f x ∂μ‖ ≤ ∫ x, ‖f x‖ ∂μ ∧
        ∀ T : E →L[ℝ] F, (∫ x, T (f x) ∂μ) = T (∫ x, f x ∂μ)) ∧
    -- compact-Haar case: continuous integrand on a compact T2 Borel space, finite measure
    (∀ {X E F : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
      [MeasurableSpace X] [BorelSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
      [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
      (μ : Measure X) [IsFiniteMeasure μ] (f : X → E),
      Continuous f →
      Integrable f μ ∧ ‖∫ x, f x ∂μ‖ ≤ ∫ x, ‖f x‖ ∂μ ∧
        ∀ T : E →L[ℝ] F, (∫ x, T (f x) ∂μ) = T (∫ x, f x ∂μ)) ∧
    (∀ {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
      (μ : Measure X) [IsFiniteMeasure μ] (a : X → E →ₗ[ℝ] ℝ) (C : ℝ),
      0 ≤ C → (∀ v, Measurable (fun x => a x v)) → (∀ x v, ‖a x v‖ ≤ C * ‖v‖) →
      ∃ A : E →L[ℝ] ℝ, (∀ v, A v = ∫ x, a x v ∂μ) ∧ ‖A‖ ≤ C * μ.real univ) ∧
    (∀ {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
      (μ : Measure X) [IsFiniteMeasure μ]
      (a : ∀ n, X → ContinuousMultilinearMap ℝ (fun _ : Fin (n+1) => E) ℝ)
      (D : ℕ → ℝ) (hD : ∀ n, 0 ≤ D n)
      (hm : ∀ n v, Measurable (fun x => a n x v))
      (hb : ∀ n x, ‖a n x‖ ≤ D n)
      (r : ℝ≥0) (hr : 0 < r) (C : ℝ) (hbound : ∀ n, D n * (r : ℝ)^n ≤ C)
      (F : X → E → E → ℝ),
      (∀ x z, ‖z‖ < r → ∀ w,
        HasSum (fun n => a n x (Fin.snoc (fun _ => z) w)) (F x z w)) →
      ∃ R : ℝ≥0, 0 < R ∧ R < r ∧
        AnalyticOnNhd ℝ (Ext025GP16AverageR27m.averagedCoefficients μ a D hm hb).sum
          (Metric.eball 0 R) ∧
        ∀ z : E, ‖z‖ < r → ∀ w : E,
          (Ext025GP16AverageR27m.averagedCoefficients μ a D hm hb).sum z w =
            ∫ x, F x z w ∂μ) := by
  exact QuantumNLS.Ext025GP16R27m.contract_GP16_fixed 

end QuantumNLS.X25GP16Spec
#print axioms QuantumNLS.X25GP16Spec.contract_GP16_fixed_spec
