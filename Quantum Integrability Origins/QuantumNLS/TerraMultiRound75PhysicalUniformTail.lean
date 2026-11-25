import QuantumNLS.TerraMultiRound75UniformTail
import QuantumNLS.TerraMultiRound73PhysicalTail

/-! Uniform physical spectral excess, including the finite sequence prefix. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open QuantumNLS.PhysicalTensor QuantumNLS.TerraMultiRound73Truncation
open QuantumNLS.TerraMultiRound73PhysicalExcess QuantumNLS.TerraMultiRound75UniformTail
namespace QuantumNLS.TerraMultiRound75PhysicalUniformTail

/-- The actual physical measures have uniformly small truncated-moment
excess when their same-order moments converge. This is an intermediate
conditional result, not an assumption in the REG-010 statement. -/
theorem physical_uniform_excess {L κ : ℝ} [Fact (0 < L)] (hκ : 0 < κ)
    (u : ℕ → L2T L) (v : L2T L) (p : ℝ) (hp : 0 ≤ p)
    (hu : Tendsto u atTop (𝓝 v))
    (his : ∀ j, Integrable (fun t : ℝ => |t| ^ p) (QuantumNLS.PhysicalQuantumMeasure.measure hκ (u j)))
    (hv : Integrable (fun t : ℝ => |t| ^ p) (QuantumNLS.PhysicalQuantumMeasure.measure hκ v))
    (hM : Tendsto (fun j => ∫ t : ℝ, |t| ^ p ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ (u j)))
      atTop (𝓝 (∫ t : ℝ, |t| ^ p ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ v)))) :
    ∀ ε > 0, ∃ k : ℕ, ∀ j,
      |(∫ t : ℝ, |t| ^ p ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ (u j))) -
        (∫ t : ℝ, min (|t| ^ p) (k : ℝ) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ (u j)))| < ε := by
  apply uniform_excess_small _ _ _ _ hM
  · intro k
    exact ((continuous_physical_truncation hκ p (k : ℝ) hp (Nat.cast_nonneg k)).tendsto v).comp hu
  · exact truncation_integral_tendsto _ p hp hv
  · intro j
    exact truncation_integral_tendsto _ p hp (his j)
  · intro j k
    have htrunc : Integrable (fun t : ℝ => min (|t| ^ p) (k : ℝ))
        (QuantumNLS.PhysicalQuantumMeasure.measure hκ (u j)) := by
      refine (his j).mono' ((continuous_abs.rpow_const (fun _ => Or.inr hp)).min continuous_const).aestronglyMeasurable ?_
      apply ae_of_all
      intro t
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (Real.rpow_nonneg (abs_nonneg t) p) (Nat.cast_nonneg k))]
      exact min_le_left _ _
    exact integral_mono htrunc (his j) (fun t => min_le_left _ _)
  · intro j k l hkl
    have htrunc : ∀ n : ℕ, Integrable (fun t : ℝ => min (|t| ^ p) (n : ℝ))
        (QuantumNLS.PhysicalQuantumMeasure.measure hκ (u j)) := by
      intro n
      refine (his j).mono' ((continuous_abs.rpow_const (fun _ => Or.inr hp)).min continuous_const).aestronglyMeasurable ?_
      apply ae_of_all
      intro t
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (Real.rpow_nonneg (abs_nonneg t) p) (Nat.cast_nonneg n))]
      exact min_le_left _ _
    exact integral_mono (htrunc k) (htrunc l) (fun t => min_le_min_left _ (Nat.cast_le.mpr hkl))

/-- The same-order power tails of all physical measures in the sequence are
uniformly small, provided the same-order moments converge. -/
theorem physical_uniform_power_tail {L κ : ℝ} [Fact (0 < L)] (hκ : 0 < κ)
    (u : ℕ → L2T L) (v : L2T L) (p : ℝ) (hp : 0 ≤ p)
    (hu : Tendsto u atTop (𝓝 v))
    (his : ∀ j, Integrable (fun t : ℝ => |t| ^ p) (QuantumNLS.PhysicalQuantumMeasure.measure hκ (u j)))
    (hv : Integrable (fun t : ℝ => |t| ^ p) (QuantumNLS.PhysicalQuantumMeasure.measure hκ v))
    (hM : Tendsto (fun j => ∫ t : ℝ, |t| ^ p ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ (u j)))
      atTop (𝓝 (∫ t : ℝ, |t| ^ p ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ v)))) :
    ∀ ε > 0, ∃ k : ℕ, ∀ j,
      (∫ t : ℝ, if 2 * (k : ℝ) < |t| ^ p then |t| ^ p else 0
        ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ (u j))) < ε := by
  intro ε hε
  obtain ⟨k, hk⟩ := physical_uniform_excess hκ u v p hp hu his hv hM (ε / 2) (by positivity)
  refine ⟨k, ?_⟩
  intro j
  let μ := QuantumNLS.PhysicalQuantumMeasure.measure hκ (u j)
  have hcont : Continuous (fun t : ℝ => |t| ^ p) := continuous_abs.rpow_const (fun _ => Or.inr hp)
  have hset : MeasurableSet {t : ℝ | 2 * (k : ℝ) < |t| ^ p} := measurableSet_lt measurable_const hcont.measurable
  have htail : Integrable (fun t : ℝ => if 2 * (k : ℝ) < |t| ^ p then |t| ^ p else 0) μ := by
    convert (his j).indicator hset using 1
    funext t
    simp [Set.indicator]
  have htrunc : Integrable (fun t : ℝ => min (|t| ^ p) (k : ℝ)) μ := by
    refine (his j).mono' (hcont.min continuous_const).aestronglyMeasurable ?_
    apply ae_of_all
    intro t
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (Real.rpow_nonneg (abs_nonneg t) p) (Nat.cast_nonneg k))]
    exact min_le_left _ _
  have hineq := integral_mono htail (((his j).sub htrunc).const_mul 2)
    (fun t => QuantumNLS.TerraMultiRound73PhysicalTail.power_tail_le_excess (|t| ^ p) (k : ℝ)
      (Real.rpow_nonneg (abs_nonneg t) p) (Nat.cast_nonneg k))
  rw [integral_const_mul] at hineq
  simp only [Pi.sub_apply] at hineq
  have hsub : (∫ t : ℝ, |t| ^ p - min (|t| ^ p) (k : ℝ) ∂μ) =
      (∫ t : ℝ, |t| ^ p ∂μ) - (∫ t : ℝ, min (|t| ^ p) (k : ℝ) ∂μ) :=
    integral_sub (his j) htrunc
  rw [hsub] at hineq
  dsimp [μ] at hineq
  have hj := hk j
  have := le_abs_self ((∫ t : ℝ, |t| ^ p ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ (u j))) -
    (∫ t : ℝ, min (|t| ^ p) (k : ℝ) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ (u j))))
  linarith

#print axioms physical_uniform_power_tail
#print axioms physical_uniform_excess
end QuantumNLS.TerraMultiRound75PhysicalUniformTail
