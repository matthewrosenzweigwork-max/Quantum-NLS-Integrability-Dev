import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic

/-! Same-order tail step: convergence of full moments and their bounded
truncations yields eventual uniform smallness of the excess moments. -/
set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology
namespace QuantumNLS.TerraMultiRound73TailConvergence

/-- A limit of truncated moments converges to the full limiting moment.
If the full moments and every fixed truncation converge along a sequence,
the truncation excess can be made uniformly small for all sufficiently
large sequence indices. -/
theorem eventual_excess_small (M : ℕ → ℝ) (M₀ : ℝ) (T : ℕ → ℕ → ℝ) (T₀ : ℕ → ℝ)
    (hM : Tendsto M atTop (𝓝 M₀))
    (hT : ∀ k, Tendsto (fun j => T j k) atTop (𝓝 (T₀ k)))
    (hT₀ : Tendsto T₀ atTop (𝓝 M₀)) :
    ∀ ε > 0, ∃ k, ∀ᶠ j in atTop, |M j - T j k| < ε := by
  intro ε hε
  have hlim : Tendsto (fun k => M₀ - T₀ k) atTop (𝓝 0) := by
    simpa using ((tendsto_const_nhds (x := M₀)).sub hT₀)
  have he : ∀ᶠ k in atTop, |M₀ - T₀ k| < ε / 2 := by
    have h := (Metric.tendsto_nhds.mp hlim) (ε / 2) (by positivity)
    simpa only [Real.dist_eq, sub_zero] using h
  obtain ⟨k, hk⟩ := he.exists
  refine ⟨k, ?_⟩
  have hdiff : Tendsto (fun j => M j - T j k) atTop (𝓝 (M₀ - T₀ k)) :=
    hM.sub (hT k)
  have hj : ∀ᶠ j in atTop, |(M j - T j k) - (M₀ - T₀ k)| < ε / 2 := by
    have h := (Metric.tendsto_nhds.mp hdiff) (ε / 2) (by positivity)
    simpa only [Real.dist_eq] using h
  filter_upwards [hj] with j hj
  have hh : |M j - T j k| ≤ |(M j - T j k) - (M₀ - T₀ k)| + |M₀ - T₀ k| := by
    convert abs_add_le ((M j - T j k) - (M₀ - T₀ k)) (M₀ - T₀ k) using 1 <;> ring_nf
  linarith

/-- A nonnegative or signed tail dominated by a fixed multiple of the excess
inherits the same eventual uniform bound. -/
theorem eventual_tail_small (M : ℕ → ℝ) (M₀ : ℝ) (T : ℕ → ℕ → ℝ) (T₀ : ℕ → ℝ)
    (tail : ℕ → ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hM : Tendsto M atTop (𝓝 M₀))
    (hT : ∀ k, Tendsto (fun j => T j k) atTop (𝓝 (T₀ k)))
    (hT₀ : Tendsto T₀ atTop (𝓝 M₀))
    (hbound : ∀ j k, tail j k ≤ C * |M j - T j k|) :
    ∀ ε > 0, ∃ k, ∀ᶠ j in atTop, tail j k < ε := by
  intro ε hε
  have hd : 0 < ε / (C + 1) := by positivity
  obtain ⟨k, hk⟩ := eventual_excess_small M M₀ T T₀ hM hT hT₀ _ hd
  refine ⟨k, ?_⟩
  filter_upwards [hk] with j hj
  have hm := mul_le_mul_of_nonneg_left (le_of_lt hj) hC
  have hdiv : C * (ε / (C + 1)) < ε := by
    have hc : 0 < C + 1 := by linarith
    rw [← mul_div_assoc, div_lt_iff₀ hc]
    nlinarith
  exact lt_of_le_of_lt ((hbound j k).trans hm) hdiv

#print axioms eventual_excess_small
#print axioms eventual_tail_small
end QuantumNLS.TerraMultiRound73TailConvergence
