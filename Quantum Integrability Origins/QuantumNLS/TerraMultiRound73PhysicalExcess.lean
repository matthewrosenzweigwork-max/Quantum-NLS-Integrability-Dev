import QuantumNLS.TerraMultiRound73Truncation
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! The same-order physical truncation consequence of moment convergence.
The latter is a premise here and still has to be proved from H^s convergence. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction
open QuantumNLS.PhysicalTensor QuantumNLS.TerraMultiRound73Truncation
open QuantumNLS.TerraMultiRound73TailConvergence
namespace QuantumNLS.TerraMultiRound73PhysicalExcess

/-- Truncated nonnegative moments converge to the full integral for every
measure at which the full moment is integrable. -/
theorem truncation_integral_tendsto (μ : Measure ℝ) (p : ℝ) (hp : 0 ≤ p)
    (h : Integrable (fun t : ℝ => |t| ^ p) μ) :
    Tendsto (fun k : ℕ => ∫ t : ℝ, min (|t| ^ p) (k : ℝ) ∂μ) atTop
      (𝓝 (∫ t : ℝ, |t| ^ p ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun t : ℝ => |t| ^ p)
  · intro k
    exact ((continuous_abs.rpow_const (fun _ => Or.inr hp)).min continuous_const).aestronglyMeasurable
  · exact h
  · intro k
    apply ae_of_all μ
    intro t
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (Real.rpow_nonneg (abs_nonneg t) p) (Nat.cast_nonneg k))]
    exact min_le_left _ _
  · apply ae_of_all μ
    intro t
    have he : ∀ᶠ k : ℕ in atTop, |t| ^ p ≤ (k : ℝ) :=
      tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (|t| ^ p))
    apply tendsto_const_nhds.congr'
    filter_upwards [he] with k hk
    exact (min_eq_left hk).symm

/-- Under L² convergence and convergence of the same physical moment, one
cutoff makes the excess small for all sufficiently large sequence indices. -/
theorem physical_excess_eventually_small {L κ : ℝ} [Fact (0 < L)] (hκ : 0 < κ)
    (u : ℕ → L2T L) (v : L2T L) (p : ℝ) (hp : 0 ≤ p)
    (hu : Tendsto u atTop (𝓝 v))
    (hv : Integrable (fun t : ℝ => |t| ^ p) (QuantumNLS.PhysicalQuantumMeasure.measure hκ v))
    (hM : Tendsto (fun j => ∫ t : ℝ, |t| ^ p ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ (u j)))
      atTop (𝓝 (∫ t : ℝ, |t| ^ p ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ v)))) :
    ∀ ε > 0, ∃ k : ℕ, ∀ᶠ j in atTop,
      |(∫ t : ℝ, |t| ^ p ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ (u j))) -
        (∫ t : ℝ, min (|t| ^ p) (k : ℝ) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ (u j)))| < ε := by
  apply eventual_excess_small _ _ _ _ hM
  · intro k
    exact ((continuous_physical_truncation hκ p (k : ℝ) hp (Nat.cast_nonneg k)).tendsto v).comp hu
  · exact truncation_integral_tendsto _ p hp hv

/-- The same conclusion for the integral of the positive excess itself,
assuming the sequence moments are finite. -/
theorem physical_excess_integral_eventually_small {L κ : ℝ} [Fact (0 < L)] (hκ : 0 < κ)
    (u : ℕ → L2T L) (v : L2T L) (p : ℝ) (hp : 0 ≤ p)
    (hu : Tendsto u atTop (𝓝 v))
    (his : ∀ j, Integrable (fun t : ℝ => |t| ^ p) (QuantumNLS.PhysicalQuantumMeasure.measure hκ (u j)))
    (hv : Integrable (fun t : ℝ => |t| ^ p) (QuantumNLS.PhysicalQuantumMeasure.measure hκ v))
    (hM : Tendsto (fun j => ∫ t : ℝ, |t| ^ p ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ (u j)))
      atTop (𝓝 (∫ t : ℝ, |t| ^ p ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ v)))) :
    ∀ ε > 0, ∃ k : ℕ, ∀ᶠ j in atTop,
      (∫ t : ℝ, (|t| ^ p - min (|t| ^ p) (k : ℝ)) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ (u j))) < ε := by
  intro ε hε
  obtain ⟨k, hk⟩ := physical_excess_eventually_small hκ u v p hp hu hv hM ε hε
  refine ⟨k, ?_⟩
  filter_upwards [hk] with j hj
  have ht : Integrable (fun t : ℝ => min (|t| ^ p) (k : ℝ))
      (QuantumNLS.PhysicalQuantumMeasure.measure hκ (u j)) := by
    refine (his j).mono' ((continuous_abs.rpow_const (fun _ => Or.inr hp)).min continuous_const).aestronglyMeasurable ?_
    apply ae_of_all
    intro t
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (Real.rpow_nonneg (abs_nonneg t) p) (Nat.cast_nonneg k))]
    exact min_le_left _ _
  rw [integral_sub (his j) ht]
  exact lt_of_le_of_lt (le_abs_self _) hj

#print axioms physical_excess_integral_eventually_small
#print axioms truncation_integral_tendsto
#print axioms physical_excess_eventually_small
end QuantumNLS.TerraMultiRound73PhysicalExcess
