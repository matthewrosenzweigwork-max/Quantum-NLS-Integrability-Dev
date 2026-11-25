import QuantumNLS.TerraMultiRound62InfiniteLimit

/-! A convergent regularized difference transfers moment finiteness. -/
set_option autoImplicit false
noncomputable section
open Filter Topology MeasureTheory
open scoped ENNReal
namespace QuantumNLS.TerraMultiRound62LimitComparison
open QuantumNLS.TerraMultiRound60Kernel QuantumNLS.TerraMultiRound62FiniteLimit
open QuantumNLS.TerraMultiRound62InfiniteLimit

theorem finite_of_difference (μ ν : Measure ℝ) (s : ℕ) (r : ℝ)
    (hlower : Integrable (fun t : ℝ => t^(2*s)) μ)
    (hν : Integrable (fun t : ℝ => t^(2*(s+1))) ν)
    (hdiff : Tendsto (fun n : ℕ => (∫ t, kernel (s+1) ((n : ℝ)+1) t ∂μ) -
      (∫ t, kernel (s+1) ((n : ℝ)+1) t ∂ν)) atTop (𝓝 r)) :
    Integrable (fun t : ℝ => t^(2*(s+1))) μ ∧
    (∫ t : ℝ, t^(2*(s+1)) ∂μ) = (∫ t : ℝ, t^(2*(s+1)) ∂ν) + r := by
  have hμ : Integrable (fun t : ℝ => t^(2*(s+1))) μ := by
    by_contra hnot
    have hinf : (∫⁻ t : ℝ, ENNReal.ofReal (t^(2*(s+1))) ∂μ) = ⊤ := by
      apply top_unique
      by_contra hne
      have hfin : HasFiniteIntegral (fun t : ℝ => t^(2*(s+1))) μ := by
        apply (hasFiniteIntegral_iff_ofReal (ae_of_all μ fun t => (even_two_mul (s+1)).pow_nonneg t)).2
        exact lt_top_iff_ne_top.mpr (by simpa using hne)
      exact hnot ⟨(by fun_prop : Continuous (fun t : ℝ => t^(2*(s+1)))).aestronglyMeasurable, hfin⟩
    exact (not_tendsto_atTop_of_tendsto_nhds hdiff) (infinite_difference μ ν s hlower hinf hν)
  refine ⟨hμ, ?_⟩
  have hfinite := (difference_tendsto μ ν (s+1) hμ hν).comp
    (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
  have heq := tendsto_nhds_unique hfinite hdiff
  linarith

#print axioms finite_of_difference
end QuantumNLS.TerraMultiRound62LimitComparison
