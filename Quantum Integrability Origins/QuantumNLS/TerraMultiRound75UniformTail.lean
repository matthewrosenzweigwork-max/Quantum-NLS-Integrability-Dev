import QuantumNLS.TerraMultiRound73TailConvergence

/-! Finite-prefix completion of the same-order truncation argument. -/
set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology
namespace QuantumNLS.TerraMultiRound75UniformTail
open QuantumNLS.TerraMultiRound73TailConvergence

/-- Convergent full moments and truncations yield a common cutoff for the
entire sequence, including its finite prefix. The hypotheses are intermediate
moment properties, not the conclusion of REG-010. -/
theorem uniform_excess_small (M : ℕ → ℝ) (M₀ : ℝ) (T : ℕ → ℕ → ℝ) (T₀ : ℕ → ℝ)
    (hM : Tendsto M atTop (𝓝 M₀))
    (hT : ∀ k, Tendsto (fun j => T j k) atTop (𝓝 (T₀ k)))
    (hT₀ : Tendsto T₀ atTop (𝓝 M₀))
    (hpoint : ∀ j, Tendsto (T j) atTop (𝓝 (M j)))
    (hle : ∀ j k, T j k ≤ M j)
    (hmono : ∀ j, Monotone (T j)) :
    ∀ ε > 0, ∃ k, ∀ j, |M j - T j k| < ε := by
  intro ε hε
  obtain ⟨k₀, hk₀⟩ := eventual_excess_small M M₀ T T₀ hM hT hT₀ ε hε
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hk₀
  have hhead : ∀ᶠ k : ℕ in atTop, ∀ j ∈ Finset.range N, |M j - T j k| < ε := by
    apply (Filter.eventually_all_finset (Finset.range N)).2
    intro j hj
    have h := (Metric.tendsto_nhds.mp (hpoint j)) ε hε
    filter_upwards [h] with k hk
    simpa only [Real.dist_eq, abs_sub_comm] using hk
  obtain ⟨k, hkhead, hkge⟩ := (hhead.and (eventually_ge_atTop k₀)).exists
  refine ⟨k, ?_⟩
  intro j
  by_cases hj : j < N
  · exact hkhead j (Finset.mem_range.mpr hj)
  · have h := hN j (Nat.le_of_not_gt hj)
    rw [abs_of_nonneg (sub_nonneg.mpr (hle j k₀))] at h
    rw [abs_of_nonneg (sub_nonneg.mpr (hle j k))]
    have hm := hmono j hkge
    linarith

#print axioms uniform_excess_small
end QuantumNLS.TerraMultiRound75UniformTail
