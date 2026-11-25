import Mathlib

/-!
# EXT-025 layer A: contract theorem for FIN-EXT025-GP-11

Exact source text (FINAL_EXTERNAL_THEOREM_INSTANCES.json, sha256
82876b0400535292c74c814f70269d4dea6778fb05d4d3066b73e8a3d0d13782, instance
`FIN-EXT025-GP-11`, "Monotone convergence for nonnegative scalar integrals and sums"):

* Hypotheses: "The scalar functions are measurable, nonnegative and increase
  pointwise; the ambient measure is fixed."
* Conclusion: "Their integrals increase to the integral of their pointwise limit,
  allowing the value infinity."
* Application wrapper (descriptive): counting measure supplies nonnegative series;
  no absolute-convergence presumption is needed for their rearrangement.

Lean reading.  Scalars are `ℝ≥0∞` (nonnegative extended reals: this contains every
nonnegative real function and permits the limit and the integrals to be `∞`).  The
ambient measure space is arbitrary.  The counting-measure clause is the same theorem
for the counting measure on an arbitrary index type with the discrete sigma algebra
(`lintegral_count`), and the rearrangement facts for nonnegative series are listed as
additional conjuncts.  No hypothesis beyond the printed ones is used.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal

namespace QuantumNLS.Ext025L

universe u v

/-- FIN-EXT025-GP-11 as a Lean theorem. -/
theorem contract_GP11 :
    -- general measure space
    (∀ (α : Type u) [MeasurableSpace α] (μ : Measure α) (f : ℕ → α → ℝ≥0∞),
      (∀ n, Measurable (f n)) → (∀ x, Monotone fun n => f n x) →
      (∀ x, Tendsto (fun n => f n x) atTop (𝓝 (⨆ n, f n x))) ∧
      Monotone (fun n => ∫⁻ x, f n x ∂μ) ∧
      Tendsto (fun n => ∫⁻ x, f n x ∂μ) atTop (𝓝 (∫⁻ x, ⨆ n, f n x ∂μ)) ∧
      (∫⁻ x, ⨆ n, f n x ∂μ) = ⨆ n, ∫⁻ x, f n x ∂μ) ∧
    -- counting measure: nonnegative series, no absolute convergence presumption
    (∀ (ι : Type v) (a : ℕ → ι → ℝ≥0∞), (∀ i, Monotone fun n => a n i) →
      Monotone (fun n => ∑' i, a n i) ∧
      Tendsto (fun n => ∑' i, a n i) atTop (𝓝 (∑' i, ⨆ n, a n i)) ∧
      (∑' i, ⨆ n, a n i) = ⨆ n, ∑' i, a n i) ∧
    -- rearrangement of nonnegative series
    (∀ (ι : Type v) (κ : Type v) (b : ι → κ → ℝ≥0∞),
      (∑' i, ∑' j, b i j) = ∑' j, ∑' i, b i j) ∧
    (∀ (ι : Type v) (κ : Type v) (e : ι ≃ κ) (c : κ → ℝ≥0∞),
      (∑' i, c (e i)) = ∑' j, c j) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro α _ μ f hf hm
    have hmon : Monotone f := fun n m hnm x => hm x hnm
    have hi : Monotone (fun n => ∫⁻ x, f n x ∂μ) :=
      fun n m hnm => lintegral_mono (hmon hnm)
    have hmct : (∫⁻ x, ⨆ n, f n x ∂μ) = ⨆ n, ∫⁻ x, f n x ∂μ := lintegral_iSup hf hmon
    refine ⟨fun x => tendsto_atTop_iSup (hm x), hi, ?_, hmct⟩
    rw [hmct]
    exact tendsto_atTop_iSup hi
  · intro ι a ha
    letI : MeasurableSpace ι := ⊤
    have hmon : Monotone a := fun n m hnm i => ha i hnm
    have hmeas : ∀ n, Measurable (a n) := fun n => measurable_from_top
    have hct := lintegral_iSup (μ := (Measure.count : Measure ι)) hmeas hmon
    simp only [lintegral_count] at hct
    have hi : Monotone (fun n => ∑' i, a n i) := by
      intro n m hnm
      exact ENNReal.tsum_le_tsum fun i => hmon hnm i
    refine ⟨hi, ?_, hct⟩
    rw [hct]
    exact tendsto_atTop_iSup hi
  · intro ι κ b
    exact ENNReal.tsum_comm
  · intro ι κ e c
    exact Equiv.tsum_eq e c

end QuantumNLS.Ext025L

#print axioms QuantumNLS.Ext025L.contract_GP11
