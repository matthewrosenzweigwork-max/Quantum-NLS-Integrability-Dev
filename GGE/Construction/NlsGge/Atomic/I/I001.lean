import Mathlib
import NlsGge.Weights.ComplexEntire

                                                                                                          
                                                                                                                             
                                                              

set_option autoImplicit false
open NlsGge.Weights Filter Topology Set

namespace NlsGge.Atomic.I001

theorem I001_main : ((
  ∀ (lower upper : ℝ) (c : ℕ → ℝ), 0 < lower → (∀ j : ℕ, lower ≤ c j) → (∀ j : ℕ, c j ≤ upper) →
    (∀ R : ℝ, TendstoUniformlyOn (fun N : ℕ => fun z : ℂ => ∑ j ∈ Finset.range N, complexWeightTerm c z j)
        (complexWeight c) atTop (Metric.closedBall (0 : ℂ) R)) ∧
    (∀ R : ℝ, TendstoUniformlyOn (fun N : ℕ => fun z : ℂ => ∑ j ∈ Finset.range N, complexWeightTermDerivative c z j)
        (fun z : ℂ => ∑' j, complexWeightTermDerivative c z j) atTop (Metric.closedBall (0 : ℂ) R)) ∧
    AnalyticOnNhd ℂ (complexWeight c) univ ∧
    (∀ r : ℝ, complexWeight c (r : ℂ) = (weight c r : ℂ))
  : Prop)) := by
  intro lower upper c hlower hbound hupper
  refine ⟨fun R => complexWeightSeries_tendstoUniformlyOn_compact lower upper c hlower hbound hupper _
      (isCompact_closedBall (0 : ℂ) R),
    fun R => complexWeightDerivativeSeries_tendstoUniformlyOn_compact lower upper c hlower hbound hupper _
      (isCompact_closedBall (0 : ℂ) R),
    fun z _ => complexWeight_analyticAt lower upper c hlower hbound hupper z,
    fun r => complexWeight_ofReal lower upper c hlower hbound hupper r⟩

end NlsGge.Atomic.I001
