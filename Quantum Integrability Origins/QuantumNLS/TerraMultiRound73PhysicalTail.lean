import QuantumNLS.TerraMultiRound73PhysicalExcess

/-! Same-order physical spectral tails, conditional on convergence of the
actual unshifted moments; Sobolev-to-moment convergence remains open. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open QuantumNLS.PhysicalTensor QuantumNLS.TerraMultiRound73PhysicalExcess
namespace QuantumNLS.TerraMultiRound73PhysicalTail

theorem power_tail_le_excess (a B : ℝ) (ha : 0 ≤ a) (hB : 0 ≤ B) :
    (if 2 * B < a then a else 0) ≤ 2 * (a - min a B) := by
  split_ifs with h
  · rw [min_eq_right (by linarith)]
    linarith
  · have := min_le_left a B
    linarith

/-- Convergence of same-order moments yields eventually uniform physical
power tails. The finiteness and convergence of those moments are explicit
intermediate premises, not hypotheses of a completed REG-010 theorem. -/
theorem physical_power_tail_eventually_small {L κ : ℝ} [Fact (0 < L)] (hκ : 0 < κ)
    (u : ℕ → L2T L) (v : L2T L) (p : ℝ) (hp : 0 ≤ p)
    (hu : Tendsto u atTop (𝓝 v))
    (his : ∀ j, Integrable (fun t : ℝ => |t| ^ p) (QuantumNLS.PhysicalQuantumMeasure.measure hκ (u j)))
    (hv : Integrable (fun t : ℝ => |t| ^ p) (QuantumNLS.PhysicalQuantumMeasure.measure hκ v))
    (hM : Tendsto (fun j => ∫ t : ℝ, |t| ^ p ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ (u j)))
      atTop (𝓝 (∫ t : ℝ, |t| ^ p ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ v)))) :
    ∀ ε > 0, ∃ k : ℕ, ∀ᶠ j in atTop,
      (∫ t : ℝ, if 2 * (k : ℝ) < |t| ^ p then |t| ^ p else 0
        ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ (u j))) < ε := by
  intro ε hε
  obtain ⟨k, hk⟩ := physical_excess_integral_eventually_small hκ u v p hp hu his hv hM (ε / 2) (by positivity)
  refine ⟨k, ?_⟩
  filter_upwards [hk] with j hj
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
    (fun t => power_tail_le_excess (|t| ^ p) (k : ℝ) (Real.rpow_nonneg (abs_nonneg t) p) (Nat.cast_nonneg k))
  rw [integral_const_mul] at hineq
  simp only [Pi.sub_apply] at hineq
  dsimp [μ] at hineq
  linarith

#print axioms power_tail_le_excess
#print axioms physical_power_tail_eventually_small
end QuantumNLS.TerraMultiRound73PhysicalTail
