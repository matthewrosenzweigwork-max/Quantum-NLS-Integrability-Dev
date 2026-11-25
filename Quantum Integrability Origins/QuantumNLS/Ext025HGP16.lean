import QuantumNLS.Ext025BIntegration
import QuantumNLS.Ext025B2AnalyticAverage

/-! EXT-025 layer A (part 2), haiku_inventory. Contract GP-16 =
FIN-EXT025-GP-16 (Banach integration on compact parameter sets and scalar
averaging of covectors), stated at the literal text of
FINAL_EXTERNAL_THEOREM_INSTANCES.json:
  hypotheses: (interval case) the Banach-valued integrand is strongly measurable
  with integrable norm; (compact-Haar case) the evaluated vector map is
  continuous from the compact group into a Banach space; (covector case) each
  scalar evaluation is measurable and uniformly bounded in the tangent norm, with
  uniform analytic coefficient bounds when analyticity is claimed;
  conclusion: the integral norm is bounded by the integral of the norm and bounded
  linear maps commute with the integral; a uniformly bounded scalar-linear average
  defines a bounded covector; uniform analytic coefficient bounds give dual-norm
  analyticity on a smaller ball.
The application wrapper of the record (fixed-vector regularity, product torus)
is consumer-side and not part of this statement. The compact-Haar construction
is taken in the record's own terms: the statement is for a finite measure on a
compact T2 Borel space and a continuous integrand. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace QuantumNLS.Ext025HGP16

/-- Exact contract GP-16 (all three hypothesis families and the analytic clause). -/
theorem contract_GP16 :
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
    -- covector case: uniformly bounded scalar evaluations give a bounded covector
    (∀ {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
      (μ : Measure X) [IsProbabilityMeasure μ] (a : X → E →ₗ[ℝ] ℝ) (C : ℝ),
      0 ≤ C → (∀ v, Measurable (fun x => a x v)) → (∀ x v, ‖a x v‖ ≤ C * ‖v‖) →
      ∃ A : E →L[ℝ] ℝ, (∀ v, A v = ∫ x, a x v ∂μ) ∧ ‖A‖ ≤ C) ∧
    -- analytic clause: uniform coefficient bounds give dual-norm analyticity on a smaller ball
    (∀ {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
      (μ : Measure X) [IsProbabilityMeasure μ]
      (a : ∀ n, X → ContinuousMultilinearMap ℝ (fun _ : Fin (n+1) => E) ℝ)
      (D : ℕ → ℝ), (∀ n, 0 ≤ D n) →
      ∀ (hm : ∀ n v, Measurable (fun x => a n x v))
        (hb : ∀ n x, ‖a n x‖ ≤ D n) (r : ℝ≥0) (C : ℝ), (∀ n, D n * (r : ℝ)^n ≤ C) →
        (r : ℝ≥0∞) ≤ (QuantumNLS.Ext025B2AnalyticAverage.averagedCoefficients μ a D hm hb).radius ∧
        AnalyticOnNhd ℝ (QuantumNLS.Ext025B2AnalyticAverage.averagedCoefficients μ a D hm hb).sum
          (Metric.eball 0 r)) := by
  refine ⟨fun {X E F} _ _ _ _ _ _ _ μ f hm hn =>
    QuantumNLS.Ext025BIntegration.«FIN-EXT025-GP-16-integrable» (μ := μ) f hm hn,
    fun {X E F} _ _ _ _ _ _ _ _ _ _ _ μ _ f hf =>
    QuantumNLS.Ext025BIntegration.«FIN-EXT025-GP-16-compact» (μ := μ) f hf,
    fun {X E} _ _ _ μ _ a C hC hm hb =>
    QuantumNLS.Ext025BIntegration.«FIN-EXT025-GP-16-covector» (μ := μ) a C hC hm hb,
    fun {X E} _ _ _ μ _ a D hD hm hb r C hbound =>
    QuantumNLS.Ext025B2AnalyticAverage.«FIN-EXT025-GP-16-coefficient-analyticity» μ a D hD hm hb r C hbound⟩

end QuantumNLS.Ext025HGP16

#print axioms QuantumNLS.Ext025HGP16.contract_GP16
