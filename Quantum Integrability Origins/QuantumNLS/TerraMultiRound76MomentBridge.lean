import QuantumNLS.TerraMultiRound75PhysicalUniformTail

/-! Weak convergence plus uniform control of truncation excess yields
same-order physical moment convergence.  Establishing that control from
Sobolev convergence remains a separate REG-010 obligation. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open QuantumNLS.PhysicalTensor QuantumNLS.TerraMultiRound73Truncation
open QuantumNLS.TerraMultiRound73PhysicalExcess
namespace QuantumNLS.TerraMultiRound76MomentBridge

/-- The standard three-term truncation argument. The tail condition must hold
for every sufficiently large cutoff; no higher moment is assumed. -/
theorem moment_convergence_of_uniform_excess {L κ : ℝ} [Fact (0 < L)]
    (hκ : 0 < κ) (u : ℕ → L2T L) (v : L2T L) (p : ℝ) (hp : 0 ≤ p)
    (hu : Tendsto u atTop (𝓝 v))
    (hv : Integrable (fun t : ℝ => |t| ^ p) (QuantumNLS.PhysicalQuantumMeasure.measure hκ v))
    (hUI : ∀ ε > 0, ∃ K : ℕ, ∀ k ≥ K, ∀ᶠ j in atTop,
      |(∫ t : ℝ, |t| ^ p ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ (u j))) -
        (∫ t : ℝ, min (|t| ^ p) (k : ℝ) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ (u j)))| < ε) :
    Tendsto (fun j => ∫ t : ℝ, |t| ^ p ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ (u j)))
      atTop (𝓝 (∫ t : ℝ, |t| ^ p ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ v))) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨K, hK⟩ := hUI (ε / 3) (by positivity)
  have hlim := truncation_integral_tendsto (QuantumNLS.PhysicalQuantumMeasure.measure hκ v) p hp hv
  have htail : ∀ᶠ k : ℕ in atTop,
      |(∫ t : ℝ, min (|t| ^ p) (k : ℝ) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ v)) -
        (∫ t : ℝ, |t| ^ p ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ v))| < ε / 3 := by
    have h := (Metric.tendsto_nhds.mp hlim) (ε / 3) (by positivity)
    simpa only [Real.dist_eq] using h
  obtain ⟨k, hk, hkt⟩ := (Filter.Eventually.and (eventually_ge_atTop K) htail).exists
  have htr := ((continuous_physical_truncation hκ p (k : ℝ) hp (Nat.cast_nonneg k)).tendsto v).comp hu
  have htr' : ∀ᶠ j in atTop,
      |(∫ t : ℝ, min (|t| ^ p) (k : ℝ) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ (u j))) -
        (∫ t : ℝ, min (|t| ^ p) (k : ℝ) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ v))| < ε / 3 := by
    have h := (Metric.tendsto_nhds.mp htr) (ε / 3) (by positivity)
    simpa only [Real.dist_eq, Function.comp_apply] using h
  filter_upwards [hK k hk, htr'] with j hj hj'
  rw [Real.dist_eq]
  have hsum := abs_add_le
    ((∫ t : ℝ, |t| ^ p ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ (u j))) -
      (∫ t : ℝ, min (|t| ^ p) (k : ℝ) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ (u j))))
    (((∫ t : ℝ, min (|t| ^ p) (k : ℝ) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ (u j))) -
      (∫ t : ℝ, min (|t| ^ p) (k : ℝ) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ v))) +
      ((∫ t : ℝ, min (|t| ^ p) (k : ℝ) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ v)) -
      (∫ t : ℝ, |t| ^ p ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ v))))
  have hsum' := abs_add_le
    ((∫ t : ℝ, min (|t| ^ p) (k : ℝ) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ (u j))) -
      (∫ t : ℝ, min (|t| ^ p) (k : ℝ) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ v)))
    ((∫ t : ℝ, min (|t| ^ p) (k : ℝ) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ v)) -
      (∫ t : ℝ, |t| ^ p ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ v)))
  have heq : (∫ t : ℝ, |t| ^ p ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ (u j))) -
      (∫ t : ℝ, |t| ^ p ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ v)) =
      ((∫ t : ℝ, |t| ^ p ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ (u j))) -
      (∫ t : ℝ, min (|t| ^ p) (k : ℝ) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ (u j)))) +
      (((∫ t : ℝ, min (|t| ^ p) (k : ℝ) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ (u j))) -
      (∫ t : ℝ, min (|t| ^ p) (k : ℝ) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ v))) +
      ((∫ t : ℝ, min (|t| ^ p) (k : ℝ) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ v)) -
      (∫ t : ℝ, |t| ^ p ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ v)))) := by ring
  rw [heq]
  linarith

/-- For a convergent L² sequence with finite same-order moments, convergence
of those moments is equivalent to uniform truncation control. This isolates
exactly the estimate still needed from Sobolev convergence. -/
theorem moment_convergence_iff_uniform_excess {L κ : ℝ} [Fact (0 < L)]
    (hκ : 0 < κ) (u : ℕ → L2T L) (v : L2T L) (p : ℝ) (hp : 0 ≤ p)
    (hu : Tendsto u atTop (𝓝 v))
    (his : ∀ j, Integrable (fun t : ℝ => |t| ^ p) (QuantumNLS.PhysicalQuantumMeasure.measure hκ (u j)))
    (hv : Integrable (fun t : ℝ => |t| ^ p) (QuantumNLS.PhysicalQuantumMeasure.measure hκ v)) :
    Tendsto (fun j => ∫ t : ℝ, |t| ^ p ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ (u j)))
      atTop (𝓝 (∫ t : ℝ, |t| ^ p ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ v))) ↔
    ∀ ε > 0, ∃ K : ℕ, ∀ k ≥ K, ∀ᶠ j in atTop,
      |(∫ t : ℝ, |t| ^ p ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ (u j))) -
        (∫ t : ℝ, min (|t| ^ p) (k : ℝ) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ (u j)))| < ε := by
  constructor
  · intro hM ε hε
    obtain ⟨K, hK⟩ := QuantumNLS.TerraMultiRound75PhysicalUniformTail.physical_uniform_excess
      hκ u v p hp hu his hv hM ε hε
    refine ⟨K, ?_⟩
    intro k hk
    filter_upwards with j
    have htr : ∀ n : ℕ, Integrable (fun t : ℝ => min (|t| ^ p) (n : ℝ))
        (QuantumNLS.PhysicalQuantumMeasure.measure hκ (u j)) := by
      intro n
      refine (his j).mono' ((continuous_abs.rpow_const (fun _ => Or.inr hp)).min continuous_const).aestronglyMeasurable ?_
      apply ae_of_all
      intro t
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (Real.rpow_nonneg (abs_nonneg t) p) (Nat.cast_nonneg n))]
      exact min_le_left _ _
    have hle := integral_mono (htr K) (htr k)
      (fun t => min_le_min_left (|t| ^ p) (Nat.cast_le.mpr hk))
    have hfull := integral_mono (htr k) (his j) (fun t => min_le_left (|t| ^ p) (k : ℝ))
    rw [abs_of_nonneg (sub_nonneg.mpr hfull)]
    have hbound := hK j
    have hKfull := integral_mono (htr K) (his j) (fun t => min_le_left (|t| ^ p) (K : ℝ))
    rw [abs_of_nonneg (sub_nonneg.mpr hKfull)] at hbound
    linarith
  · exact moment_convergence_of_uniform_excess hκ u v p hp hu hv

#print axioms moment_convergence_iff_uniform_excess
#print axioms moment_convergence_of_uniform_excess
end QuantumNLS.TerraMultiRound76MomentBridge
