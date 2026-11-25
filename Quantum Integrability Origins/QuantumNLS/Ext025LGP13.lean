import Mathlib

/-!
# EXT-025 layer A: contract theorem for FIN-EXT025-GP-13

Exact source text (FINAL_EXTERNAL_THEOREM_INSTANCES.json, sha256
82876b0400535292c74c814f70269d4dea6778fb05d4d3066b73e8a3d0d13782, instance
`FIN-EXT025-GP-13`, "Dominated convergence in scalar integrals and Fourier square sums"):

* Hypotheses: "The measurable scalar functions converge pointwise almost everywhere
  and are dominated in absolute value by one integrable function on a fixed measure
  space."
* Conclusion: "The integrals converge; applying this to norms or squares gives the
  indicated norm convergence."
* Normalization: "The measure and integrable majorant are specified per application;
  a bound that depends on the limiting parameter is not sufficient."

Lean reading.  "Scalar" is any `RCLike` field (real or complex).  "Measurable" is
weakened to `AEStronglyMeasurable` (a weaker hypothesis, hence a stronger theorem).
The domination is a single integrable `b : α → ℝ` with `‖f n x‖ ≤ b x` almost
everywhere for every `n`.  Conclusions: the limit is integrable, the integrals converge,
and the norm error converges to zero (`L¹`).  For the square clause the dominating
function bounds `‖f n x‖^2` (the theorem applied to the squares `‖f n - g‖^2`), giving
the `L²`-type error convergence.  The last two conjuncts are the same statements on a
counting measure (Fourier square sums) over an arbitrary index type with a summable
majorant.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal

namespace QuantumNLS.Ext025L

universe u v

/-- FIN-EXT025-GP-13 as a Lean theorem. -/
theorem contract_GP13 :
    -- dominated convergence for the integrals and the L¹ error
    (∀ (𝕜 : Type) [RCLike 𝕜] (α : Type u) [MeasurableSpace α] (μ : Measure α)
      (f : ℕ → α → 𝕜) (g : α → 𝕜) (b : α → ℝ),
      (∀ n, AEStronglyMeasurable (f n) μ) → Integrable b μ →
      (∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ b x) →
      (∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) →
      Integrable g μ ∧
      Tendsto (fun n => ∫ x, f n x ∂μ) atTop (𝓝 (∫ x, g x ∂μ)) ∧
      Tendsto (fun n => ∫ x, ‖f n x - g x‖ ∂μ) atTop (𝓝 0)) ∧
    -- the same applied to squares: squared domination gives squared-norm convergence
    (∀ (𝕜 : Type) [RCLike 𝕜] (α : Type u) [MeasurableSpace α] (μ : Measure α)
      (f : ℕ → α → 𝕜) (g : α → 𝕜) (b : α → ℝ),
      (∀ n, AEStronglyMeasurable (f n) μ) → Integrable b μ →
      (∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ^ 2 ≤ b x) →
      (∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) →
      (∀ᵐ x ∂μ, ‖g x‖ ^ 2 ≤ b x) ∧
      Tendsto (fun n => ∫ x, ‖f n x - g x‖ ^ 2 ∂μ) atTop (𝓝 0)) ∧
    -- counting measure on an arbitrary index set: Fourier-type sums
    (∀ (𝕜 : Type) [RCLike 𝕜] (ι : Type v) (f : ℕ → ι → 𝕜) (g : ι → 𝕜) (b : ι → ℝ),
      Summable b → (∀ n i, ‖f n i‖ ≤ b i) →
      (∀ i, Tendsto (fun n => f n i) atTop (𝓝 (g i))) →
      Tendsto (fun n => ∑' i, f n i) atTop (𝓝 (∑' i, g i)) ∧
      Tendsto (fun n => ∑' i, ‖f n i - g i‖) atTop (𝓝 0)) ∧
    (∀ (𝕜 : Type) [RCLike 𝕜] (ι : Type v) (f : ℕ → ι → 𝕜) (g : ι → 𝕜) (b : ι → ℝ),
      Summable b → (∀ n i, ‖f n i‖ ^ 2 ≤ b i) →
      (∀ i, Tendsto (fun n => f n i) atTop (𝓝 (g i))) →
      Tendsto (fun n => ∑' i, ‖f n i - g i‖ ^ 2) atTop (𝓝 0)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro 𝕜 _ α _ μ f g b hf hb hbound hlim
    have hg : AEStronglyMeasurable g μ := aestronglyMeasurable_of_tendsto_ae atTop hf hlim
    have hgb : ∀ᵐ x ∂μ, ‖g x‖ ≤ b x := by
      have hall : ∀ᵐ x ∂μ, (∀ n, ‖f n x‖ ≤ b x) ∧
          Tendsto (fun n => f n x) atTop (𝓝 (g x)) := by
        filter_upwards [ae_all_iff.mpr hbound, hlim] with x h1 h2 using ⟨h1, h2⟩
      filter_upwards [hall] with x ⟨h1, h2⟩
      exact le_of_tendsto h2.norm (Eventually.of_forall h1)
    have hint : Integrable g μ := hb.mono' hg hgb
    refine ⟨hint, tendsto_integral_of_dominated_convergence b hf hb hbound hlim, ?_⟩
    have h := tendsto_integral_of_dominated_convergence (fun x => 2 * b x)
      (F := fun n x => ‖f n x - g x‖) (f := fun _ => (0 : ℝ))
      (fun n => (hf n).sub hg |>.norm) (hb.const_mul 2) ?_ ?_
    · simpa using h
    · intro n
      filter_upwards [hbound n, hgb] with x h1 h2
      calc ‖‖f n x - g x‖‖ = ‖f n x - g x‖ := norm_norm _
        _ ≤ ‖f n x‖ + ‖g x‖ := norm_sub_le _ _
        _ ≤ 2 * b x := by linarith
    · filter_upwards [hlim] with x hx
      have := (tendsto_sub_nhds_zero_iff.mpr hx).norm
      simpa using this
  · intro 𝕜 _ α _ μ f g b hf hb hbound hlim
    have hg : AEStronglyMeasurable g μ := aestronglyMeasurable_of_tendsto_ae atTop hf hlim
    have hgb : ∀ᵐ x ∂μ, ‖g x‖ ^ 2 ≤ b x := by
      have hall : ∀ᵐ x ∂μ, (∀ n, ‖f n x‖ ^ 2 ≤ b x) ∧
          Tendsto (fun n => f n x) atTop (𝓝 (g x)) := by
        filter_upwards [ae_all_iff.mpr hbound, hlim] with x h1 h2 using ⟨h1, h2⟩
      filter_upwards [hall] with x ⟨h1, h2⟩
      exact le_of_tendsto (h2.norm.pow 2) (Eventually.of_forall h1)
    refine ⟨hgb, ?_⟩
    have h := tendsto_integral_of_dominated_convergence (fun x => 4 * b x)
      (F := fun n x => ‖f n x - g x‖ ^ 2) (f := fun _ => (0 : ℝ))
      (fun n => ((hf n).sub hg |>.norm).pow 2) (hb.const_mul 4) ?_ ?_
    · simpa using h
    · intro n
      filter_upwards [hbound n, hgb] with x h1 h2
      have h3 : ‖f n x - g x‖ ^ 2 ≤ (‖f n x‖ + ‖g x‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le _ _) 2
      have h4 : (‖f n x‖ + ‖g x‖) ^ 2 ≤ 2 * ‖f n x‖ ^ 2 + 2 * ‖g x‖ ^ 2 := by
        nlinarith [sq_nonneg (‖f n x‖ - ‖g x‖)]
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      linarith
    · filter_upwards [hlim] with x hx
      have := ((tendsto_sub_nhds_zero_iff.mpr hx).norm).pow 2
      simpa using this
  · intro 𝕜 _ ι f g b hb hbound hlim
    have hgb : ∀ i, ‖g i‖ ≤ b i := fun i =>
      le_of_tendsto (hlim i).norm (Eventually.of_forall fun n => hbound n i)
    refine ⟨tendsto_tsum_of_dominated_convergence hb hlim (Eventually.of_forall hbound), ?_⟩
    have h := tendsto_tsum_of_dominated_convergence
      (𝓕 := atTop) (f := fun n i => ‖f n i - g i‖) (g := fun _ => (0 : ℝ)) (bound := fun i => 2 * b i)
      (hb.mul_left 2) ?_ ?_
    · simpa using h
    · intro i
      have := (tendsto_sub_nhds_zero_iff.mpr (hlim i)).norm
      simpa using this
    · refine Eventually.of_forall fun n i => ?_
      calc ‖‖f n i - g i‖‖ = ‖f n i - g i‖ := norm_norm _
        _ ≤ ‖f n i‖ + ‖g i‖ := norm_sub_le _ _
        _ ≤ 2 * b i := by linarith [hbound n i, hgb i]
  · intro 𝕜 _ ι f g b hb hbound hlim
    have hgb : ∀ i, ‖g i‖ ^ 2 ≤ b i := fun i =>
      le_of_tendsto ((hlim i).norm.pow 2) (Eventually.of_forall fun n => hbound n i)
    have h := tendsto_tsum_of_dominated_convergence
      (𝓕 := atTop) (f := fun n i => ‖f n i - g i‖ ^ 2) (g := fun _ => (0 : ℝ)) (bound := fun i => 4 * b i)
      (hb.mul_left 4) ?_ ?_
    · simpa using h
    · intro i
      have := ((tendsto_sub_nhds_zero_iff.mpr (hlim i)).norm).pow 2
      simpa using this
    · refine Eventually.of_forall fun n i => ?_
      have h3 : ‖f n i - g i‖ ^ 2 ≤ (‖f n i‖ + ‖g i‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le _ _) 2
      have h4 : (‖f n i‖ + ‖g i‖) ^ 2 ≤ 2 * ‖f n i‖ ^ 2 + 2 * ‖g i‖ ^ 2 := by
        nlinarith [sq_nonneg (‖f n i‖ - ‖g i‖)]
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      linarith [hbound n i, hgb i]

end QuantumNLS.Ext025L

#print axioms QuantumNLS.Ext025L.contract_GP13
