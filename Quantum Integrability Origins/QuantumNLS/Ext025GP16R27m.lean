import QuantumNLS.Ext025HGP16
import QuantumNLS.Ext025GP16AverageR27m
/-! GP-16 with arbitrary finite compact parameter measures and actual scalar
Taylor average identification on a positive ball. Total mass is retained. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal
namespace QuantumNLS.Ext025GP16R27m
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]

 theorem finite_covector (μ : Measure X) [IsFiniteMeasure μ]
    (a : X → E →ₗ[ℝ] ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hm : ∀ v, Measurable (fun x => a x v)) (hb : ∀ x v, ‖a x v‖ ≤ C * ‖v‖) :
    ∃ A : E →L[ℝ] ℝ, (∀ v, A v = ∫ x, a x v ∂μ) ∧ ‖A‖ ≤ C * μ.real univ := by
  have hi (v : E) : Integrable (fun x => a x v) μ :=
    Integrable.of_bound (hm v).aestronglyMeasurable (C * ‖v‖)
      (Eventually.of_forall (fun x => hb x v))
  let l : E →ₗ[ℝ] ℝ :=
    { toFun := fun v => ∫ x, a x v ∂μ
      map_add' := fun v w => by
        simp_rw [map_add]
        exact integral_add (hi v) (hi w)
      map_smul' := fun c v => by simp [integral_const_mul] }
  have hl (v : E) : ‖l v‖ ≤ (C * μ.real univ) * ‖v‖ := by
    simpa only [l, LinearMap.coe_mk, AddHom.coe_mk, mul_assoc, mul_comm, mul_left_comm] using
      norm_integral_le_of_norm_le_const (μ := μ) (Eventually.of_forall (fun x => hb x v))
  exact ⟨l.mkContinuous (C * μ.real univ) hl, fun _ => rfl,
    LinearMap.mkContinuous_norm_le _ (mul_nonneg hC ENNReal.toReal_nonneg) _⟩

/-- All three integration cases and the identified analytic scalar average. -/
theorem contract_GP16_fixed :
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
  refine ⟨fun {X E F} _ _ _ _ _ _ _ μ f hm hn =>
    Ext025BIntegration.«FIN-EXT025-GP-16-integrable» (μ := μ) f hm hn,
    fun {X E F} _ _ _ _ _ _ _ _ _ _ _ μ _ f hf =>
      Ext025BIntegration.«FIN-EXT025-GP-16-compact» (μ := μ) f hf,
    fun {X E} _ _ _ μ _ a C hC hm hb => finite_covector μ a C hC hm hb, ?_⟩
  intro X E _ _ _ μ _ a D hD hm hb r hr C hbound F hTaylor
  have h := Ext025GP16AverageR27m.«FIN-EXT025-GP-16-analytic-average»
    μ a D hD hm hb r hr C hbound F hTaylor
  refine ⟨r/2, by positivity, by simpa using half_lt_self hr, ?_, h.2⟩
  exact h.1.mono (Metric.eball_subset_eball (by exact_mod_cast (half_le_self r.2)))
end QuantumNLS.Ext025GP16R27m
#print axioms QuantumNLS.Ext025GP16R27m.contract_GP16_fixed
