import QuantumNLS.EnergyTracePassage
import QuantumNLS.Ext025HGP12
import QuantumNLS.Ext025B8BorelCalculus

/-! Round 27 GP-12. Positive operator truncations are continuous under trace
norm convergence by the proved trace ideal estimate. Their supremum is the
spectral form expectation, including infinite energy. No test continuity input. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace
namespace QuantumNLS.Ext025GP12R27m
open TraceClass TraceIdeal Ext025STrace Ext025B7GentleCompression EnergyTracePassage
open BetheChargeResolution Ext025B6PVM Ext025B8BorelCalculus
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The positive density's scalar spectral measure, summed over a complete basis.
No finite energy assumption enters this definition. -/
def densityMeasure (P : ProjectionMeasure E) (b : HilbertBasis ι ℂ E)
    (ρ : E →L[ℂ] E) : Measure ℝ :=
  Measure.sum (fun i => scalarMeasure P (CFC.sqrt ρ (b i)))

def formEnergy (P : ProjectionMeasure E) (b : HilbertBasis ι ℂ E)
    (w : ℝ → ℝ≥0∞) (ρ : E →L[ℂ] E) : ℝ≥0∞ := ∫⁻ t, w t ∂densityMeasure P b ρ

/-- The bounded positive operator test is exactly its spectral form expectation. -/
theorem bounded_energy (P : ProjectionMeasure E) (b : HilbertBasis ι ℂ E)
    (ρ : E →L[ℂ] E) (hρ : ρ.IsPositive) (f : ℝ → ℂ) (hf : Measurable f)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ t, ‖f t‖ ≤ C) :
    posTrace (bounded P f hf C hC hb * ρ * (bounded P f hf C hC hb).adjoint) =
      formEnergy P b (fun t => ENNReal.ofReal (‖f t‖^2)) ρ := by
  rw [block_trace_hs b ρ _ hρ]
  unfold hsSq formEnergy densityMeasure
  rw [lintegral_sum_measure]
  apply tsum_congr
  intro i
  exact (vectorIntegral_esquare P f (CFC.sqrt ρ (b i))
    (MemLp.of_bound hf.aestronglyMeasurable C (.of_forall hb)))

/-- Monotone bounded spectral truncations recover the unbounded form energy. -/
theorem energy_sup (P : ProjectionMeasure E) (b : HilbertBasis ι ℂ E)
    (ρ : E →L[ℂ] E) (hρ : ρ.IsPositive)
    (f : ℕ → ℝ → ℂ) (hf : ∀ n, Measurable (f n))
    (C : ℕ → ℝ) (hC : ∀ n, 0 ≤ C n) (hb : ∀ n t, ‖f n t‖ ≤ C n)
    (hm : Monotone (fun n t => ENNReal.ofReal (‖f n t‖^2))) :
    formEnergy P b (fun t => ⨆ n, ENNReal.ofReal (‖f n t‖^2)) ρ =
      ⨆ n, posTrace (bounded P (f n) (hf n) (C n) (hC n) (hb n) * ρ *
        (bounded P (f n) (hf n) (C n) (hC n) (hb n)).adjoint) := by
  simp_rw [bounded_energy P b ρ hρ]
  exact lintegral_iSup (fun n => by fun_prop) hm

variable {J : Type*} {l : Filter J} [l.NeBot]

/-- Trace norm convergence proves convergence of every bounded positive test. -/
theorem bounded_test_limit (b : HilbertBasis ι ℂ E) (B : E →L[ℂ] E)
    (ρ : J → E →L[ℂ] E) (σ : E →L[ℂ] E)
    (hρ : ∀ n, (ρ n).IsPositive ∧ IsTraceClass (ρ n))
    (hσ : σ.IsPositive ∧ IsTraceClass σ)
    (ht : Tendsto (fun n => traceNorm (ρ n - σ)) l (𝓝 0)) :
    Tendsto (fun n => posTrace (B * ρ n * B.adjoint)) l
      (𝓝 (posTrace (B * σ * B.adjoint))) := by
  have hc : Tendsto (fun n => ENNReal.ofReal (‖B‖^2) * traceNorm (ρ n-σ))
      l (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (‖B‖^2)) ht
      (Or.inr ENNReal.ofReal_ne_top)
    simpa using this
  have hs : Tendsto (fun n => traceNorm (B * ρ n * B.adjoint - B * σ * B.adjoint))
      l (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hc
      (fun n => zero_le)
    intro n
    change traceNorm (B * ρ n * B.adjoint - B * σ * B.adjoint) ≤
      ENNReal.ofReal (‖B‖^2) * traceNorm (ρ n-σ)
    rw [← sub_mul, ← mul_sub]
    have h := traceNorm_mul_mul_le B (ρ n-σ) B.adjoint
    simpa only [LinearIsometryEquiv.norm_map, pow_two, ENNReal.ofReal_mul (norm_nonneg B), mul_assoc, mul_comm, mul_left_comm] using h
  have hsr := (ENNReal.tendsto_toReal (by simp)).comp hs
  have hr : Tendsto (fun n => (posTrace (B * ρ n * B.adjoint)).toReal) l
      (𝓝 (posTrace (B * σ * B.adjoint)).toReal) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hz : Tendsto (fun n => |total (B * ρ n * B.adjoint) - total (B * σ * B.adjoint)|)
        l (𝓝 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsr
        (fun n => abs_nonneg _)
      intro n
      exact total_difference b _ _ (block_positive _ _ (hρ n).1)
        (block_positive _ _ hσ.1)
        (by simpa only [IsTraceClass, traceNorm_of_isPositive (block_positive _ _ (hρ n).1)]
          using lt_top_iff_ne_top.mpr (block_finite _ _ (hρ n).1 (hρ n).2))
        (by simpa only [IsTraceClass, traceNorm_of_isPositive (block_positive _ _ hσ.1)]
          using lt_top_iff_ne_top.mpr (block_finite _ _ hσ.1 hσ.2))
    simpa only [Real.norm_eq_abs, total] using hz
  exact (ENNReal.tendsto_toReal_iff (fun n => block_finite _ _ (hρ n).1 (hρ n).2)
    (block_finite _ _ hσ.1 hσ.2)).mp hr

/-- Exact GP-12 operator-to-energy bridge. The truncation property is expressed
by the supremum of the squared spectral symbols; no continuity of tests or
boundedness across all states is assumed. -/
theorem spectral_energy_lsc (P : ProjectionMeasure E) (b : HilbertBasis ι ℂ E)
    (f : ℕ → ℝ → ℂ) (hf : ∀ n, Measurable (f n))
    (C : ℕ → ℝ) (hC : ∀ n, 0 ≤ C n) (hb : ∀ n t, ‖f n t‖ ≤ C n)
    (hm : Monotone (fun n t => ENNReal.ofReal (‖f n t‖^2)))
    (ρ : J → E →L[ℂ] E) (σ : E →L[ℂ] E)
    (hρ : ∀ n, (ρ n).IsPositive ∧ IsTraceClass (ρ n))
    (hσ : σ.IsPositive ∧ IsTraceClass σ)
    (ht : Tendsto (fun n => traceNorm (ρ n-σ)) l (𝓝 0)) :
    formEnergy P b (fun t => ⨆ n, ENNReal.ofReal (‖f n t‖^2)) σ ≤
      liminf (fun k => formEnergy P b (fun t => ⨆ n, ENNReal.ofReal (‖f n t‖^2)) (ρ k)) l := by
  simp_rw [energy_sup P b _ hσ.1 f hf C hC hb hm]
  calc
    _ = ⨆ n, liminf (fun k => posTrace (bounded P (f n) (hf n) (C n) (hC n) (hb n) *
        ρ k * (bounded P (f n) (hf n) (C n) (hC n) (hb n)).adjoint)) l := by
      apply iSup_congr
      intro n
      exact (bounded_test_limit b _ ρ σ hρ hσ ht).liminf_eq.symm
    _ ≤ liminf (fun k => ⨆ n, posTrace (bounded P (f n) (hf n) (C n) (hC n) (hb n) *
        ρ k * (bounded P (f n) (hf n) (C n) (hC n) (hb n)).adjoint)) l :=
      iSup_liminf_le_liminf_iSup
    _ = _ := by
      congr 1
      ext k
      exact (energy_sup P b (ρ k) (hρ k).1 f hf C hC hb hm).symm

/-- Every nonnegative real spectral weight has canonical bounded root truncations. -/
def cutoff (h : ℝ → ℝ) (n : ℕ) (t : ℝ) : ℂ := (Real.sqrt (min (h t) (n : ℝ)) : ℂ)

theorem cutoff_measurable (h : ℝ → ℝ) (hmeas : Measurable h) (n : ℕ) :
    Measurable (cutoff h n) := by
  unfold cutoff
  fun_prop

theorem cutoff_square (h : ℝ → ℝ) (hh : ∀ t, 0 ≤ h t) (n : ℕ) (t : ℝ) :
    ‖cutoff h n t‖^2 = min (h t) (n : ℝ) := by
  simp only [cutoff, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (le_min (hh t) (Nat.cast_nonneg n))]

theorem cutoff_bound (h : ℝ → ℝ) (n : ℕ) (t : ℝ) : ‖cutoff h n t‖ ≤ Real.sqrt n := by
  simpa only [cutoff, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)] using Real.sqrt_le_sqrt (min_le_right (h t) (n : ℝ))

theorem cutoff_sup (h : ℝ → ℝ) (hh : ∀ t, 0 ≤ h t) (t : ℝ) :
    (⨆ n, ENNReal.ofReal (‖cutoff h n t‖^2)) = ENNReal.ofReal (h t) := by
  simp_rw [cutoff_square h hh]
  apply le_antisymm
  · exact iSup_le (fun n => ENNReal.ofReal_le_ofReal (min_le_left _ _))
  · obtain ⟨n,hn⟩ := exists_nat_ge (h t)
    exact (by rw [min_eq_left hn] : ENNReal.ofReal (h t) ≤
      ENNReal.ofReal (min (h t) (n : ℝ))).trans (le_iSup (fun m : ℕ => ENNReal.ofReal (min (h t) (m : ℝ))) n)

def cutoffOperator (P : ProjectionMeasure E) (h : ℝ → ℝ) (hmeas : Measurable h) (n : ℕ) :
    E →L[ℂ] E := bounded P (cutoff h n) (cutoff_measurable h hmeas n)
      (Real.sqrt n) (Real.sqrt_nonneg _) (cutoff_bound h n)

/-- The same bounded truncations identify the vector quadratic form. -/
theorem vector_energy_sup (P : ProjectionMeasure E) (h : ℝ → ℝ)
    (hh : ∀ t, 0 ≤ h t) (hmeas : Measurable h) (x : E) :
    Ext025B7PVMForms.energy P (fun t => ENNReal.ofReal (h t)) x =
      ⨆ n, ENNReal.ofReal (‖cutoffOperator P h hmeas n x‖^2) := by
  have hm : Monotone (fun n t => ENNReal.ofReal (‖cutoff h n t‖^2)) := by
    intro i j hij t
    change ENNReal.ofReal (‖cutoff h i t‖^2) ≤ ENNReal.ofReal (‖cutoff h j t‖^2)
    rw [cutoff_square h hh, cutoff_square h hh]
    exact ENNReal.ofReal_le_ofReal (min_le_min le_rfl (Nat.cast_le.mpr hij))
  calc
    _ = ∫⁻ t, ⨆ n, ENNReal.ofReal (‖cutoff h n t‖^2) ∂scalarMeasure P x := by
      simp only [Ext025B7PVMForms.energy, cutoff_sup h hh]
    _ = ⨆ n, ∫⁻ t, ENNReal.ofReal (‖cutoff h n t‖^2) ∂scalarMeasure P x :=
      lintegral_iSup (fun n => by unfold cutoff; fun_prop) hm
    _ = _ := by
      apply iSup_congr
      intro n
      exact (vectorIntegral_esquare P (cutoff h n) x
        (MemLp.of_bound (cutoff_measurable h hmeas n).aestronglyMeasurable (Real.sqrt n)
          (.of_forall (cutoff_bound h n)))).symm

theorem vector_energy_lowerSemicontinuous (P : ProjectionMeasure E) (h : ℝ → ℝ)
    (hh : ∀ t, 0 ≤ h t) (hmeas : Measurable h) :
    LowerSemicontinuous (Ext025B7PVMForms.energy P (fun t => ENNReal.ofReal (h t))) := by
  have he : Ext025B7PVMForms.energy P (fun t => ENNReal.ofReal (h t)) =
      fun x : E => ⨆ n, ENNReal.ofReal (‖cutoffOperator P h hmeas n x‖^2) :=
    funext (vector_energy_sup P h hh hmeas)
  rw [he]
  apply lowerSemicontinuous_iSup
  intro n
  have hc : Continuous (fun x : E => ENNReal.ofReal (‖cutoffOperator P h hmeas n x‖^2)) :=
    ENNReal.continuous_ofReal.comp ((cutoffOperator P h hmeas n).continuous.norm.pow 2)
  exact hc.lowerSemicontinuous

/-- No truncation family is an input: canonical bounded root cutoffs prove
lower semicontinuity of every nonnegative measurable spectral form energy. -/
theorem form_energy_lsc (P : ProjectionMeasure E) (b : HilbertBasis ι ℂ E)
    (h : ℝ → ℝ) (hh : ∀ t, 0 ≤ h t) (hmeas : Measurable h)
    (ρ : J → E →L[ℂ] E) (σ : E →L[ℂ] E)
    (hρ : ∀ n, (ρ n).IsPositive ∧ IsTraceClass (ρ n))
    (hσ : σ.IsPositive ∧ IsTraceClass σ)
    (ht : Tendsto (fun n => traceNorm (ρ n-σ)) l (𝓝 0)) :
    formEnergy P b (fun t => ENNReal.ofReal (h t)) σ ≤
      liminf (fun k => formEnergy P b (fun t => ENNReal.ofReal (h t)) (ρ k)) l := by
  have hm : Monotone (fun n t => ENNReal.ofReal (‖cutoff h n t‖^2)) := by
    intro i j hij t
    change ENNReal.ofReal (‖cutoff h i t‖^2) ≤ ENNReal.ofReal (‖cutoff h j t‖^2)
    rw [cutoff_square h hh, cutoff_square h hh]
    exact ENNReal.ofReal_le_ofReal (min_le_min le_rfl (Nat.cast_le.mpr hij))
  have htst := spectral_energy_lsc P b (cutoff h) (cutoff_measurable h hmeas)
    (fun n => Real.sqrt n) (fun n => Real.sqrt_nonneg _) (cutoff_bound h) hm ρ σ hρ hσ ht
  simpa only [cutoff_sup h hh] using htst

/-- Topological lower semicontinuity whenever the state topology is the trace
norm topology (or any finer topology), stated by its neighborhood convergence
property. This premise concerns the state topology, never continuity of tests. -/
theorem form_energy_lowerSemicontinuous {X : Type*} [TopologicalSpace X]
    (P : ProjectionMeasure E) (b : HilbertBasis ι ℂ E)
    (h : ℝ → ℝ) (hh : ∀ t, 0 ≤ h t) (hmeas : Measurable h)
    (ρ : X → E →L[ℂ] E)
    (hρ : ∀ x, (ρ x).IsPositive ∧ IsTraceClass (ρ x))
    (ht : ∀ x, Tendsto (fun y => traceNorm (ρ y-ρ x)) (𝓝 x) (𝓝 0)) :
    LowerSemicontinuous (fun x => formEnergy P b (fun t => ENNReal.ofReal (h t)) (ρ x)) := by
  rw [lowerSemicontinuous_iff_le_liminf]
  intro x
  exact form_energy_lsc P b h hh hmeas ρ (ρ x) hρ (hρ x) (ht x)

/-- Scalar Fatou and the proved positive-operator spectral form-energy bridge. -/
theorem contract_GP12_fixed :
    (∀ {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : ℕ → α → ℝ≥0∞),
      (∀ n, Measurable (f n)) →
      (∫⁻ x, liminf (fun n => f n x) atTop ∂μ) ≤ liminf (fun n => ∫⁻ x, f n x ∂μ) atTop) ∧
    (∀ (P : ProjectionMeasure E) (b : HilbertBasis ι ℂ E)
      (h : ℝ → ℝ), (∀ t, 0 ≤ h t) → Measurable h →
      ∀ (ρ : ℕ → E →L[ℂ] E) (σ : E →L[ℂ] E),
      (∀ n, (ρ n).IsPositive ∧ IsTraceClass (ρ n)) →
      σ.IsPositive ∧ IsTraceClass σ →
      Tendsto (fun n => traceNorm (ρ n-σ)) atTop (𝓝 0) →
      formEnergy P b (fun t => ENNReal.ofReal (h t)) σ ≤
        liminf (fun k => formEnergy P b (fun t => ENNReal.ofReal (h t)) (ρ k)) atTop) ∧
    (∀ {X : Type*} [TopologicalSpace X] (P : ProjectionMeasure E) (b : HilbertBasis ι ℂ E)
      (h : ℝ → ℝ), (∀ t, 0 ≤ h t) → Measurable h →
      ∀ (ρ : X → E →L[ℂ] E), (∀ x, (ρ x).IsPositive ∧ IsTraceClass (ρ x)) →
      (∀ x, Tendsto (fun y => traceNorm (ρ y-ρ x)) (𝓝 x) (𝓝 0)) →
      LowerSemicontinuous (fun x => formEnergy P b (fun t => ENNReal.ofReal (h t)) (ρ x))) ∧
    (∀ (P : ProjectionMeasure E) (h : ℝ → ℝ), (∀ t, 0 ≤ h t) → Measurable h →
      LowerSemicontinuous (Ext025B7PVMForms.energy P (fun t => ENNReal.ofReal (h t)))) :=
  ⟨fun {α} _ μ f hf => Ext025BMeasure.«FIN-EXT025-GP-12» (μ := μ) f hf,
    form_energy_lsc, form_energy_lowerSemicontinuous, vector_energy_lowerSemicontinuous⟩
end QuantumNLS.Ext025GP12R27m
#print axioms QuantumNLS.Ext025GP12R27m.contract_GP12_fixed
